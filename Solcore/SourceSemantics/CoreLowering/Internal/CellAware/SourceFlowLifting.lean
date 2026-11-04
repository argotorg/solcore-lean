import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageStatements
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControlShape
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion

/-!
# Lifting Source traces over cell-aware flows

Body lifting from independent ordinary Source execution at the mixed physical scope, by statement form, recording the exact prefix reached by a stage rejection.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyLiftBounds
/-! Body lifting starts from independent ordinary Source execution at the actual
mixed physical scope. It records the exact reached prefix of a stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

def Lifts {administrative : Core.Context}
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) (statements : List StatementId) : Prop :=
    ∀ {size},
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    RecursiveNamedCallBounds.FunctionOutcome program size context invocation.evidence invocation.source environment before
      statements finalContext outcome after →
    SelectedCompilationStageBodyLiftBounds.BodyLift program registry true invocation context environment before
      statements finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPlainInversion
/-! The ordinary Source declaration copies its environment, captures one
principal descriptor over the copies and allocates it once. Its compiler-supported direct lambda excludes the genuine
unsupported-initializer fault without evaluating the initializer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPlainInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds

variable {program : Program} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem selected (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {other}
    (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

theorem value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ captured middle function location, size = SourceExecutionSize.stepSize [] ∧ finalContext = nextContext ∧
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.EnvironmentCopies source environment before captured middle ∧
      Dynamic.GeneralizedClosureCaptures context source captured binder initializer function ∧
      Dynamic.Heap.AllocatesGeneralized middle function location after := by
  cases trace <;> have same := selected unique found (by assumption) <;> subst_vars <;> simp_all
  rename_i captures snapshot _ extension allocated
  have equal := Dynamic.BinderExtends.functional extended extension
  exact ⟨equal.symm, _, _, snapshot, _, captures, allocated⟩

theorem fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (capturable : ∃ function, Dynamic.GeneralizedClosureCaptures context source environment binder initializer function)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) : False := by
  cases trace
  case missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  all_goals have same := selected unique found (by assumption)
  all_goals subst_vars
  all_goals simp_all
  rename_i equal _ unsupported _
  obtain ⟨rfl, rfl⟩ := equal
  obtain ⟨function, captures⟩ := capturable
  exact Dynamic.GeneralizedInitializerUnsupported.not_captures unsupported captures

private theorem empty_trace {mode : Bool} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} :
    PlainStatements program mode (SourceExecutionSize.stepSize []) invocation context environment heap
      [] context (.fallthrough environment) heap := by
  cases mode <;> exact .control .nil

theorem generalized {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (capturable : ∃ function, Dynamic.GeneralizedClosureCaptures context invocation.source environment binder initializer function)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize captured middle function location bound,
      tailSize < size ∧ Dynamic.EnvironmentCopies invocation.source environment before captured middle ∧
      Dynamic.GeneralizedClosureCaptures context invocation.source captured binder initializer function ∧
      Dynamic.Heap.AllocatesGeneralized middle function location bound ∧
      PlainStatements program mode tailSize invocation nextContext ((binder.id, location) :: environment)
        bound rest finalContext outcome after := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, _, _, _, _, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, _, tailStrict, head, tail⟩
  · exact (fault unique found form polymorphic capturable failed).elim
  · obtain ⟨captured, middle, function, location, rfl, equalContext, equalOutcome, snapshot, captures, allocated⟩ :=
      value unique found form polymorphic extended head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · exact ⟨SourceExecutionSize.stepSize [], captured, middle, function, location, after, strict, snapshot, captures,
        allocated, empty_trace⟩
  · obtain ⟨captured, snapshotHeap, function, location, _, equalContext, equalOutcome, snapshot, captures, allocated⟩ :=
      value unique found form polymorphic extended head
    subst middleContext
    cases equalOutcome
    exact ⟨tailSize, captured, snapshotHeap, function, location, middle, tailStrict, snapshot, captures, allocated, tail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPlainInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceGeneralizedPrefixLifting
/-! A genuine generalized Source declaration copies its environment and creates
the actual mixed physical prefix before the remaining ordinary Source
statements are lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceGeneralizedPrefixLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open TypedLexicalWhile (initializedRequest sequence)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private theorem head_typed {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (source named) context (id :: rest)) :
    ∃ control final facts, StatementHasType (source named) control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩

include bindings record registered in
theorem generalized {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {lambdaBody rest : List StatementId} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr}
    {body : Expr} {childFuel : Nat} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = [])
      (coercions : initializerNode.coercions = [])
      (site : CellAwareSourceBodyAdmission.Site whole.indexed.base.locals named.signature.key [] (source named) binder initializer)
      (initial : GeneralizedLocalInitializerPackets.Receipt whole.indexed
        (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
          (CallableIndexedNamedGeneration.context whole.indexed named) scope initializer reasonAt) site.binding [] lowered)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      {captured : Expr}
      (copied : SourceCoreSourceCells.copyScope (some (CallableIndexedNamedGeneration.allocator whole.indexed named))
        (source named) scope (fun index => index)
        (CellAwareGeneralizedSnapshotCode.snapshotInner lowered.type lowered.expression annotation.expression) =
          .ok captured)
    (sourceEq : invocation.source = source named)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt)
    (remaining : CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, lowered.type) :: scope) rest) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  let descriptor := Dynamic.GeneralizedClosure.ofDirectLambda context (source named) environment binder initializer
    parameters result lambdaBody
  have captures : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer descriptor :=
    .directLambda (lookupExpression?_sound initializerFound) initializerForm
      (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
  obtain ⟨tailSize, copies, snapshotHeap, function, location, bound, _strict, snapshot, actualCaptures, allocated, tail⟩ :=
    CellAwareGeneralizedPlainInversion.generalized (mode := true) (invocation := invocation) (by simpa only [sourceEq] using unique)
      (by simpa only [sourceEq] using found) form polymorphic (by simpa only [sourceEq] using extended)
      ⟨descriptor, by simpa only [sourceEq] using captures⟩ trace
  have snapshotNamed : Dynamic.EnvironmentCopies (source named) environment before copies snapshotHeap := by
    simpa only [sourceEq] using snapshot
  have capturesNamed : Dynamic.GeneralizedClosureCaptures context (source named) copies binder initializer function := by
    simpa only [sourceEq] using actualCaptures
  obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
  have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshotNamed.agrees locals)
    headTyped found form polymorphic capturesNamed
  obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, _agreement, _smaller, nextEnvironments, nextHeaps,
      nextLocals, nextAgrees, nextTyped, _preserved, _effect, nextAuthority, reached, _related, nextAdmitted, nextPhysical,
      locationEq, nativeEq⟩ :=
    CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initial issuer declaration polymorphic extended
      ordinary nativeTyped allocation annotation same copied producer bindings registered environments heaps locals agrees
      actualTyped current admitted authority physical ready snapshotNamed capturesNamed
      functionTyped allocated type body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, adapted⟩ :=
    remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
  exact ⟨resultContext, resultOutcome, resultHeap,
    .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form snapshot actualCaptures polymorphic
      (by simpa only [sourceEq] using extended) allocated stagedTail, adapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceGeneralizedPrefixLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceTerminalLifting
/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

theorem terminal {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceEq : invocation.source = source named)
    (head : Head invocation id statements)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    (certified : certificates scope id lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope statements := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner ownerFrame _ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal invocation.source id statements := by
    cases head with
    | returning rest contains form => exact .returning rest (lookupStatement?_complete unique contains) form
    | tail contains form => exact .tail (lookupStatement?_complete unique contains) form
  obtain ⟨childSize, childOutcome, _strict, rfl, rfl, child⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique terminal trace
  exact SelectedCompilationStageBodyLiftBounds.terminal_expression head
    (children runtime covers sameLedger childSize certified found typed environments heaps locals agrees actualTyped
      initial admitted authority physical owner ownerFrame child)

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceTerminalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceOrdinaryPrefixLifting
/-! A real ordinary Source initializer is lifted before allocation. A failed
or rejected child keeps its reached heap, and successful allocation retains
all earlier generalized descriptors for the actual Source suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceOrdinaryPrefixLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open TypedLexicalWhile (initializedRequest sequence)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


include registered in
theorem initialized {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {rest : List StatementId} {type : Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {body : Expr} {administrative : Core.Context}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) context initializer initializerNode.type)
      (value : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (childLift : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation (certificates context) size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation (certificates context) faults size)
    (remaining : CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, lowered.type) :: scope) rest) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  have contains : ContainsStatement invocation.source id node := by simpa only [sourceEq] using lookupStatement?_sound found
  rcases SelectedCompilationStageLexicalInversion.initialized (mode := true) (invocation := invocation)
      (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, reason, _strict, contextEq, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, _childStrict, _tailStrict, child, allocated, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | completed => exact ⟨_, _, _, .letFault contains form mono lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached => exact ⟨_, _, _, .letFault contains form mono lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | rejected origin call reason reached => exact ⟨_, _, _, .letFault contains form mono lifted, .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, _expressionRelated, post⟩ :=
        preservation runtime covers sameLedger stageSize value
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation measured
      cases represented with
      | value payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical,
            CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location,
            CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
          remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
            (runtime.transport (.ofBinderExtends extended))
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
            (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
            reachedState nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
        exact ⟨resultContext, resultOutcome, resultHeap,
          .letInitialized contains form lifted mono (by simpa only [sourceEq] using extended) allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceOrdinaryPrefixLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceAbsentPrefixLifting
/-! An original uninitialized declaration lifts through its actual absent
cell allocation. The independently executed suffix starts at that exact heap,
with every earlier generalized descriptor still retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceAbsentPrefixLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open TypedLexicalControl (absentRequest)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


include registered in
theorem absent {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {rest : List StatementId}
    {payload : Ty} {body : Expr} {administrative : Core.Context}
    (found : (source named).lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends (source named).owner context binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (absentRequest (source named) scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (absentRequest (source named) scope binder payload))
    (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (remaining : CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, payload) :: scope) rest) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  have contains : ContainsStatement invocation.source id node := by simpa only [sourceEq] using lookupStatement?_sound found
  obtain ⟨tailSize, location, bound, _smaller, allocated, tail⟩ :=
    SelectedCompilationStageLexicalInversion.absent (mode := true) (invocation := invocation)
      (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
      (by simpa only [sourceEq] using extended) trace
  obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
      projection environments heaps locals agrees actualTyped current admitted authority physical
      (ready current physical.read) allocated body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
    remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reachedState nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
  exact ⟨resultContext, resultOutcome, resultHeap,
    .letUninitialized contains form mono (by simpa only [sourceEq] using extended) allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceAbsentPrefixLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
/-! Body lifting starts from independent ordinary Source execution at the actual
mixed physical scope. It records the exact reached prefix of a stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

def Lifts {administrative : Core.Context}
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) (mode : Bool) (statements : List StatementId) : Prop :=
    ∀ {size},
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    SelectedCompilationStageScopedLiftBounds.PlainStatements program mode size invocation context environment before
      statements finalContext outcome after →
    SelectedCompilationStageBodyLiftBounds.BodyLift program registry mode invocation context environment before
      statements finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
/-! Independent Source lifting follows the actual mixed physical state after
an expression or scoped branch. Exact descriptor effects preserve the owning
frame and its allocation readiness at every reached continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

def Ready (environment : Dynamic.Environment) (canonical actual : Environment)
    (actualContext : Core.Context) (embedding : Renaming) (heap : Dynamic.Heap) : Prop :=
  ∃ mapping world store,
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions ∧
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world heap store ∧
    Dynamic.EnvironmentAgrees heap context.locals environment ∧
    EnvironmentsAgree embedding canonical actual ∧
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions ∧
    Dynamic.SourceRuntimeValid program context (source named) ∧ invocation.evidence.Covers context ∧
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements ∧
    ∃ initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩,
      Admission bridge context initial ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
        named.signature.key [] mapping world heap store environment ∧
      ∃ (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world heap store environment)
        (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys),
        owner.key.frameLocation = physical.location ∧
        ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native

variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem test_value {child : Nat} {before after : Dynamic.Heap} {value : Dynamic.Value}
    {certificate : GenericExpressionMeaning.Certificate} {test : ExpressionId} {node : ExpressionNode} {code : Expr}
    (children : ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool,code⟩)
    (ready : ReadyAt before)
    (trace : SourceExecutionSize.ExpressionEvaluates program child context invocation.evidence invocation.source
      environment before test value after) :
    (∃ origin call reason reached, Staging.Recursive.Expression program registry invocation context environment before test
      (.fault (.stage origin call reason)) reached) ∨
    (Staging.Recursive.Expression program registry invocation context environment before test (.value value) after ∧
      ReadyAt after ∧ Dynamic.BooleanValue value) := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨staged,reached,lifted,adapted⟩ := children child generated found typed
    environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.value trace)
  cases adapted with
  | rejected origin call reason reached => exact .inl ⟨origin,call,reason,reached,lifted⟩
  | completed =>
    obtain ⟨size,measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    obtain ⟨_,finalStore,finalMap,finalWorld,_,represented,finalHeaps,maps,worlds,preserved,metadata,effect,
      last,_,post⟩ := preservation size generated found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation measured
    have boolean : Dynamic.BooleanValue value := by
      cases represented with
      | value payload =>
        obtain ⟨truth,same,_⟩ := booleans (nodeType ▸ payload)
        rw [same]
        trivial
    exact .inr ⟨lifted,⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
      locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
      last,post.at_value.2,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩,boolean⟩

theorem body_prefix {size : Nat} {before after : Dynamic.Heap}
    {statements : List StatementId} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (ready : ReadyAt before)
    (trace : RecursiveNamedCallBounds.StatementsOutcome program size context invocation.evidence invocation.source
      environment before statements finalContext outcome after) :
    BodyLift program registry false invocation context environment before statements finalContext outcome after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  exact body environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation allocationReady trace

theorem body_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (preservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type code size)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program registry false invocation context environment before statements
      finalContext (.fallthrough finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨size,measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_,finalStore,finalMap,finalWorld,_,_,finalHeaps,maps,worlds,preserved,metadata,effect,
    last,_,post⟩ := preservation size environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation allocationReady measured
  exact ⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
    locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
    last,post,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceTransferLifting
/-! Actual break and continue statements have the same independent Source
and staged control outcome, with no heap or physical history change. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceTransferLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

theorem breaking {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
      environment before (id :: rest) finalContext outcome after := by
    cases mode <;> exact trace.sound
  obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.breaking_view unique found form ordinary
  exact ⟨_, _, _, .breaking (lookupStatement?_sound found) form, .completed (.breaking environment)⟩

theorem continuing {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
      environment before (id :: rest) finalContext outcome after := by
    cases mode <;> exact trace.sound
  obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.continuing_view unique found form ordinary
  exact ⟨_, _, _, .continuing (lookupStatement?_sound found) form, .completed (.continuing environment)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceTransferLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowGeneralizedLifting
/-! A genuine generalized Source declaration copies its environment and creates
the actual mixed physical prefix before the remaining ordinary Source
statements are lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowGeneralizedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open TypedLexicalWhile (initializedRequest sequence)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private theorem head_typed {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (source named) context (id :: rest)) :
    ∃ control final facts, StatementHasType (source named) control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩

include bindings record registered in
theorem generalized {mode : Bool} {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {lambdaBody rest : List StatementId} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr}
    {body : Expr} {childFuel : Nat} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = [])
      (coercions : initializerNode.coercions = [])
      (site : CellAwareSourceBodyAdmission.Site whole.indexed.base.locals named.signature.key [] (source named) binder initializer)
      (initial : GeneralizedLocalInitializerPackets.Receipt whole.indexed
        (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
          (CallableIndexedNamedGeneration.context whole.indexed named) scope initializer reasonAt) site.binding [] lowered)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      {captured : Expr}
      (copied : SourceCoreSourceCells.copyScope (some (CallableIndexedNamedGeneration.allocator whole.indexed named))
        (source named) scope (fun index => index)
        (CellAwareGeneralizedSnapshotCode.snapshotInner lowered.type lowered.expression annotation.expression) =
          .ok captured)
    (sourceEq : invocation.source = source named)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, lowered.type) :: scope) mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  let descriptor := Dynamic.GeneralizedClosure.ofDirectLambda context (source named) environment binder initializer
    parameters result lambdaBody
  have captures : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer descriptor :=
    .directLambda (lookupExpression?_sound initializerFound) initializerForm
      (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
  obtain ⟨tailSize, copies, snapshotHeap, function, location, bound, _strict, snapshot, actualCaptures, allocated, tail⟩ :=
    CellAwareGeneralizedPlainInversion.generalized (mode := mode) (invocation := invocation) (by simpa only [sourceEq] using unique)
      (by simpa only [sourceEq] using found) form polymorphic (by simpa only [sourceEq] using extended)
      ⟨descriptor, by simpa only [sourceEq] using captures⟩ trace
  have snapshotNamed : Dynamic.EnvironmentCopies (source named) environment before copies snapshotHeap := by
    simpa only [sourceEq] using snapshot
  have capturesNamed : Dynamic.GeneralizedClosureCaptures context (source named) copies binder initializer function := by
    simpa only [sourceEq] using actualCaptures
  obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
  have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime (snapshotNamed.agrees locals)
    headTyped found form polymorphic capturesNamed
  obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, _agreement, _smaller, nextEnvironments, nextHeaps,
      nextLocals, nextAgrees, nextTyped, _preserved, _effect, nextAuthority, reached, _related, nextAdmitted, nextPhysical,
      locationEq, nativeEq⟩ :=
    CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initial issuer declaration polymorphic extended
      ordinary nativeTyped allocation annotation same copied producer bindings registered environments heaps locals agrees
      actualTyped current admitted authority physical ready snapshotNamed capturesNamed
      functionTyped allocated type body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, adapted⟩ :=
    remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
  exact ⟨resultContext, resultOutcome, resultHeap,
    .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form snapshot actualCaptures polymorphic
      (by simpa only [sourceEq] using extended) allocated stagedTail, adapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowGeneralizedLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowOrdinaryLifting
/-! A real ordinary Source initializer is lifted before allocation. A failed
or rejected child keeps its reached heap, and successful allocation retains
all earlier generalized descriptors for the actual Source suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowOrdinaryLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open TypedLexicalWhile (initializedRequest sequence)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


include registered in
theorem initialized {mode : Bool} {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {rest : List StatementId} {type : Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {body : Expr} {administrative : Core.Context}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) context initializer initializerNode.type)
      (value : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (childLift : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation (certificates context) size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation (certificates context) faults size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, lowered.type) :: scope) mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  have contains : ContainsStatement invocation.source id node := by simpa only [sourceEq] using lookupStatement?_sound found
  rcases SelectedCompilationStageLexicalInversion.initialized (mode := mode) (invocation := invocation)
      (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
      (by simpa only [sourceEq] using extended) trace with
    ⟨childSize, reason, _strict, contextEq, outcomeEq, child⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, _childStrict, _tailStrict, child, allocated, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | completed => exact ⟨_, _, _, .letFault contains form mono lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached => exact ⟨_, _, _, .letFault contains form mono lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ := childLift runtime covers sameLedger childSize value
      (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
      environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation child
    cases adapted with
    | rejected origin call reason reached => exact ⟨_, _, _, .letFault contains form mono lifted, .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, _expressionRelated, post⟩ :=
        preservation runtime covers sameLedger stageSize value
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped current admitted authority physical owner sameLocation measured
      cases represented with
      | value payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical,
            CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location,
            CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
          remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
            (runtime.transport (.ofBinderExtends extended))
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
            (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
            reachedState nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
        exact ⟨resultContext, resultOutcome, resultHeap,
          .letInitialized contains form lifted mono (by simpa only [sourceEq] using extended) allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowOrdinaryLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAbsentLifting
/-! An original uninitialized declaration lifts through its actual absent
cell allocation. The independently executed suffix starts at that exact heap,
with every earlier generalized descriptor still retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAbsentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open TypedLexicalControl (absentRequest)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


include registered in
theorem absent {mode : Bool} {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {rest : List StatementId}
    {payload : Ty} {body : Expr} {administrative : Core.Context}
    (found : (source named).lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends (source named).owner context binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (absentRequest (source named) scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (absentRequest (source named) scope binder payload))
    (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, payload) :: scope) mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  have contains : ContainsStatement invocation.source id node := by simpa only [sourceEq] using lookupStatement?_sound found
  obtain ⟨tailSize, location, bound, _smaller, allocated, tail⟩ :=
    SelectedCompilationStageLexicalInversion.absent (mode := mode) (invocation := invocation)
      (by simpa only [sourceEq] using unique) (by simpa only [sourceEq] using found) form mono
      (by simpa only [sourceEq] using extended) trace
  obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
      projection environments heaps locals agrees actualTyped current admitted authority physical
      (ready current physical.read) allocated body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
    remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reachedState nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
  exact ⟨resultContext, resultOutcome, resultHeap,
    .letUninitialized contains form mono (by simpa only [sourceEq] using extended) allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAbsentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowTerminalLifting
/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

theorem nil {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode [] := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.nil trace
  exact ⟨_, .fallthrough environment, _, .nil, .completed (.fallthrough environment)⟩

theorem return_unit {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.return_unit
    (sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique) found form trace
  exact ⟨_, .returned .unit, _, .returnUnit (lookupStatement?_sound found) form, .completed (.returned .unit)⟩

theorem terminal {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {id : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceEq : invocation.source = source named)
    (head : Head invocation id mode statements)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    (certified : certificates scope id lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode statements := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner ownerFrame _ready
    finalContext outcome after trace
  obtain ⟨childSize, plain, _strict, rfl, rfl, evaluated⟩ :=
    SelectedCompilationStageScopedTerminalInversion.child_of_body
      (sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique) head trace
  have lifted := children runtime covers sameLedger childSize certified found typed
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
  obtain ⟨stagedSize, staged, reached, stagedTrace, adapted⟩ := lifted.sized
  refine ⟨_, _, reached, (head.trace stagedTrace).sound, ?_⟩
  cases adapted with
  | completed => cases plain with
    | value value => exact .completed (.returned value)
    | fault reason => exact .completed (.fault reason)
  | rejected origin call reason reached => exact .rejected origin call reason _ reached

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowTerminalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowDiscardLifting
/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowDiscardLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

variable {faults : RecursiveStageMeaning.FaultRep}

theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode semicolon : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (discarded : semicolon = true ∨ mode = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates scope expression lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificates faults size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner ownerFrame ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have suffix := ProtectedStateImperativeStatementSuffixTyping.discard
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  rcases SelectedCompilationStageDiscardInversion.child_and_tail unique found form discarded trace with
    ⟨childSize, reason, _strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, _strict, _tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, effect, middleState, _related, post⟩ :=
        preservation runtime covers sameLedger stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted authority physical owner ownerFrame measured
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        runtime covers sameLedger suffix middleState post.at_value.2
        (authority.transport effect) (physical.transport effect framePreserved) owner ownerFrame ready tail
      refine ⟨nextContext, result, finalHeap, ?_, restAdapted⟩
      rcases discarded with rfl | rfl
      · exact .discard (lookupStatement?_sound found) form lifted restTrace
      · cases semicolon with
        | false => exact .discardValue (lookupStatement?_sound found) form lifted restTrace
        | true => exact .discard (lookupStatement?_sound found) form lifted restTrace

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowDiscardLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowBlockLifting
/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowBlockLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

open SelectedCompilationStageScopedLiftBounds (PlainStatements)
variable {faults : RecursiveStageMeaning.FaultRep}

theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId} {node : StatementNode}
    {expected : TypeSystem.Ty} {type : Ty} {innerCode : Expr}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (preservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type innerCode size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner ownerFrame ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨headSize, reason, strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨innerSize, innerContext, innerStrict, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_fault unique found form failed
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
      initial admitted authority physical owner ownerFrame ready
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext (.fault reason) after from .fault innerTrace)
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, outcomeEq, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst finalContext
    subst outcome
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
      initial admitted authority physical owner ownerFrame ready
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext innerOutcome after from .control innerTrace)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched with
      | returned value =>
        exact ⟨context, _, _, .blockReturned (lookupStatement?_sound found) form lifted, .completed (.returned value)⟩
      | breaking innerEnvironment =>
        exact ⟨context, _, _, .blockBreaking (lookupStatement?_sound found) form lifted, .completed (.breaking environment)⟩
      | continuing innerEnvironment =>
        exact ⟨context, _, _, .blockContinuing (lookupStatement?_sound found) form lifted, .completed (.continuing environment)⟩
      | fault reason =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        rcases stopped with impossible | rfl
        · cases impossible
        · exact ⟨context, _, _, .blockFallthrough (lookupStatement?_sound found) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, restored, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl, Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
        environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner ownerFrame ready
        (show PlainStatements program false innerSize invocation context environment before statements
          innerContext (.fallthrough innerEnvironment) middle from .control innerTrace)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
      | completed matched =>
        cases matched
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace lifted
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, effect, middleState, _related, post⟩ :=
          preservation stagedSize environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
            initial admitted authority physical owner ownerFrame ready measured
        obtain ⟨lastContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          runtime covers sameLedger suffixTyped middleState post
          (authority.transport effect) (physical.transport effect framePreserved) owner ownerFrame ready tail
        exact ⟨lastContext, result, finalHeap, .blockFallthrough (lookupStatement?_sound found) form lifted restTrace,
          restAdapted⟩

    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowBlockLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowConditionalLifting
/-! Ordinary Source conditions and exactly the selected branch reach the same
mixed physical continuation. Genuine earlier stage rejection retains its
actual heap and bypasses the remaining branch and suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowConditionalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open CallableIndexedNamedGeneration (source)
open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

/-- All child contracts are closed by the actual common compiler tree. -/
theorem lifts {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {mode : Bool} {id : StatementId} {rest left : List StatementId} {right : Option (List StatementId)}
    {statement : StatementNode} {test : ExpressionId} {node : ExpressionNode}
    {testCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
    {expected : TypeSystem.Ty} {type : Ty} {branchCode : Bool → Expr}
    (sourceEq : invocation.source = source named)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .ifThen test left right)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool,testCode⟩)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificate faults size)
    (branches : ∀ truth : Bool, CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false (if truth then left else right.getD []))
    (branchPreservation : ∀ (truth : Bool) size, CellAwareScopeFlowBounds.PreservesAt
      bridge context model named producer registry invocation faults administrative scope false
      (if truth then left else right.getD []) expected type (branchCode truth) size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation allocationReady finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ready : Ready (named := named) (administrative := administrative) (invocation := invocation)
      (context := context) (scope := scope) bridge producer environment canonical actual actualContext embedding before :=
    ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
      initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩
  have branchTyped (truth : Bool) := ProtectedStateImperativeTypedSourceSites.branch_typed truth (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have children := children runtime covers sameLedger
  have preservation := preservation runtime covers sameLedger
  have notTail : ∀ expression, statement.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound notTail trace with
    ⟨headSize, reason, _strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, _strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, _strict, _tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    rcases SelectedCompilationStageConditionalSourceInversion.fault unique statementFound form failed with
      ⟨testSize, _testStrict, failedTest⟩ |
      ⟨testSize, value, actualType, _testStrict, reasonEq, evaluated, nonboolean, _valueType⟩ |
      ⟨testSize, branchSize, truth, testHeap, innerContext, _testStrict, _branchStrict, evaluated, failedBranch⟩
    · obtain ⟨staged, reached, lifted, adapted⟩ := children testSize generated found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.fault failedTest)
      cases adapted with
      | completed => exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .completed (.fault reason)⟩
      | rejected origin call reason reached =>
        exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call reason context reached⟩
    · rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨_lifted, _ready, boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · exact False.elim (nonboolean boolean)
    · rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge producer
          (branches truth) (branchTyped truth) testReady
          (.fault failedBranch)
        cases adapted with
        | completed matched =>
          cases matched
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.fault reason)⟩
        | rejected origin call reason reachedContext reached =>
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .rejected origin call reason context reached⟩
  · obtain ⟨testSize, branchSize, truth, testHeap, innerContext, innerOutcome,
        _testStrict, _branchStrict, contextEq, outcomeEq, evaluated, branchTrace⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique statementFound form executed
    subst finalContext
    subst outcome
    rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
      ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
    · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call stageReason context reached⟩
    · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge producer
        (branches truth) (branchTyped truth) testReady
        (.control branchTrace)
      cases adapted with
      | rejected origin call reason reachedContext reached =>
        exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
          .rejected origin call reason context reached⟩
      | completed matched =>
        cases matched with
        | returned value =>
          exact ⟨context, _, _, .ifReturned (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.returned value)⟩
        | breaking innerEnvironment =>
          exact ⟨context, _, _, .ifBreaking (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.breaking environment)⟩
        | continuing innerEnvironment =>
          exact ⟨context, _, _, .ifContinuing (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.continuing environment)⟩
        | fault reason =>
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.fault reason)⟩
        | fallthrough innerEnvironment =>
          rcases stopped with impossible | rfl
          · cases impossible
          · exact ⟨context, _, _, .ifFallthrough (lookupStatement?_sound statementFound) form liftedTest lifted .nil,
              .completed (.fallthrough environment)⟩
  · obtain ⟨testSize, branchSize, truth, testHeap, innerContext, innerOutcome,
        _testStrict, _branchStrict, contextEq, restored, evaluated, branchTrace⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique statementFound form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl, Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge producer
          (branches truth) (branchTyped truth) testReady
          (.control branchTrace)
        cases adapted with
        | rejected origin call reason reachedContext reached =>
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .rejected origin call reason context reached⟩
        | completed matched =>
          cases matched
          have nextReady := body_ready bridge producer (branchPreservation truth) (branchTyped truth) testReady lifted
          obtain ⟨nextMap,nextWorld,nextStore,nextEnvironments,nextHeaps,nextLocals,nextAgrees,nextTyped,
            nextRuntime,nextCovers,nextLedger,nextState,nextAdmitted,nextAuthority,nextPhysical,nextOwner,nextLocation,nextAllocationReady⟩ := nextReady
          obtain ⟨lastContext,result,finalHeap,restTrace,restAdapted⟩ := remaining
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextRuntime nextCovers nextLedger suffixTyped
            nextState nextAdmitted nextAuthority nextPhysical nextOwner nextLocation nextAllocationReady tail
          exact ⟨lastContext,result,finalHeap,
            .ifFallthrough (lookupStatement?_sound statementFound) form liftedTest lifted restTrace,restAdapted⟩
    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowConditionalLifting
end
