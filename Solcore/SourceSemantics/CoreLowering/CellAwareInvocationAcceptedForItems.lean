import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedInputs
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostDiscard
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedAllocation
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAssignment
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedAssignment
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostBitNot
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostProjectedBitNot
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialDiscard
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedAllocation
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAssignment
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedAssignment
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialBitNot
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialProjectedBitNot
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
import Solcore.SourceSemantics.CoreLowering.TypedImperativeNative

/-! The actual accepted `for` header items close the mixed-cell header flows.
Each item uses the compiler's own child lowering and allocation receipt;
header declarations are authenticated by the original compilation receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedForItems
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open AcceptedNamedBodyFlow (Items)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedSourceFacts (expression_node)

section Coverage
variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {result : Ty} {reasonAt : ExpressionId → Word}
  {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
  {finalScope : SourceCoreLocalCell.Scope} {finish : Expr}

/-- Header items closed below. Raw write receipts that were not refined are
outside the closure, and writes require the compiler view to be the original
Source, as for named rows. -/
def ItemsCovered (semantic : TypedSource) {fuel scope items code}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : Prop :=
  match tree with
  | .nil .. => True
  | .absent _ remaining _ => ItemsCovered semantic remaining
  | @Items.initialized _ _ _ _ _ _ _ _ _ _ binder _ _ _ _ _ _ _ _ _ remaining _ =>
      binder.scheme.quantified = [] ∧ ItemsCovered semantic remaining
  | .discard _ _ remaining => ItemsCovered semantic remaining
  | .assigned remaining _ _ | .projectedAssigned remaining _ _ | .bitNotted remaining _ _
    | .projectedBitNotted remaining _ _ => source = semantic ∧ ItemsCovered semantic remaining
  | .assigning .. | .bitNotting .. => False

end Coverage

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

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

section Validity
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {budget : Nat}

theorem post_preserves_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope items expected type code budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope items expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

theorem post_reflects_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope items expected type code budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope items expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

end Validity

section InitialValidity
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {budget : Nat}

theorem initial_preserves_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope items test postItems statements expected type code
        budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model index
      producer registry invocation faults administrative scope items test postItems statements expected type code
      budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

theorem initial_reflects_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope items test postItems statements expected type code
        budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model index
      producer registry invocation faults administrative scope items test postItems statements expected type code
      budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

end InitialValidity

section Empty
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}

/-- An exhausted update list falls through at the original lexical state. -/
theorem post_empty (budget : Nat) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope [] expected type (LocalLoop.fallthrough type) budget ∧
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope [] expected type (LocalLoop.fallthrough type) budget := by
  have evaluates : ∀ (actual : Environment) (store : Store) (embedding : Renaming),
      Evaluates actual store ((LocalLoop.fallthrough type).rename embedding) (LocalLoop.fallthroughValue type) store :=
    fun actual store _ => by simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store
  refine ⟨?_, ?_⟩
  · intro size _ mapping world actualContext environment canonical actual before store embedding
      _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
      initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
    cases trace
    exact ⟨_, store, mapping, world, evaluates actual store embedding, .fallthrough environment (.inl rfl), heaps,
      .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, protocol.refl initial, admitted⟩
  · intro size _ mapping world actualContext environment canonical actual before store embedding value finalStore
      _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
      initial admitted _authority _physical _owner _sameLocation _ready completed
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (evaluates actual store embedding)
    exact ⟨_, context, .done environment, before, mapping, world, .empty, .fallthrough environment (.inl rfl), heaps,
      .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Empty

include bindings transport registered in
/-- Induction over the accepted update items of one actual `for` statement.
The parent statement and the original compilation authenticate declarations. -/
theorem post_correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    {parentId : StatementId} {statement : StatementNode}
    {allInitial allPost : List ForItemForm} {condition : ExpressionId} {bodyStatements : List StatementId}
    (parentReached : index.Reached (.statement parentId))
    (parentFound : index.compilerSource.lookupStatement? parentId = some statement)
    (parentForm : statement.form = .forLoop allInitial condition allPost bodyStatements)
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {expected : TypeSystem.Ty} :
    ∀ {fuel scope items code}
      (tree : Items index.policy index.compilerSource (.occurrence parentId.occurrence) index.result index.reasonAt
        next finalScope (LocalLoop.fallthrough index.result) fuel scope items code),
      ItemsCovered index.source tree →
      (∀ item ∈ items, item ∈ allInitial ++ allPost) →
      ∀ {control : ControlContext} {context final : SourceSemantics.Context},
        context.signatures = whole.compatible.checked.signatures →
        ForItemsHaveType index.source control context items final →
        (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope items expected index.result code budget ∧
        CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope items expected index.result code budget := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  intro fuel scope items code tree
  induction tree with
  | nil same accepted =>
    intro _ _ control context final _ _ _
    exact post_empty bridge index producer registry invocation faults administrative budget
  | @absent fuel scope binder payload rest tail code projected remaining allocated tailIH =>
    intro covered members control context final signatures typed native
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    cases headTyped with
    | letUninitialized mono _ extended =>
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    have payloadProjected := CellAwareInvocationAcceptedSourceFacts.binder_projected index mono projected
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForPostAcceptedAllocation.absent_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.1,
      CellAwareInvocationForPostAcceptedAllocation.absent_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.2⟩
  | @initialized fuel scope binder expression payload rest tail code projected child generated childType
      remaining allocated tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨mono, covered⟩ := covered
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    have typedInitializer : ExpressionHasType index.source context expression binder.scheme.body ∧
        BinderExtends index.source.owner context binder middle := by
      cases headTyped with
      | letInitialized initializerTyped _ _ extension => exact ⟨initializerTyped, extension⟩
      | letInitializedGeneralized polymorphic => exact False.elim (polymorphic mono)
    obtain ⟨initializerTyped, extended⟩ := typedInitializer
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    obtain ⟨initializerNode, initializerFound, valueType, initializerTyped⟩ :=
      expression_node sourceUnique initializerTyped
    have payloadEq : payload = child.type := ensure_eq childType
    subst payloadEq
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForPostAcceptedAllocation.initialized_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).1)
        tailBounds.1,
      CellAwareInvocationForPostAcceptedAllocation.initialized_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).2)
        tailBounds.2⟩
  | @discard fuel scope expression rest tail child generated remaining tailIH =>
    intro covered members control context final signatures typed native
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | expression expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostDiscard.preserves bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostDiscard.reflects bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | assigning => intro covered; cases covered
  | @assigned fuel scope assignment operator expression rest tail code remaining receipt targetType tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bare_head index
      (sameSource.trans sourceEq.symm) unique receipt targetType (sourceEq ▸ assignmentTyped) administrative
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have token : AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token)
        operator head.invalid := by
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.operands (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostAssignment.preserves bridge transport functions
          producer sourceEq unique head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostAssignment.reflects bridge transport functions
          producer sourceEq unique head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @projectedAssigned fuel scope assignment operator expression rest tail code remaining receipt route tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have shapes := fun (sourceTyped : SourceAssignmentHasType invocation.source context assignment operator expression)
        {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
        (initial : protocol.State initialIndex) =>
      writes.placeDiagnostics.assignment head (.header found parentForm (members _ (List.mem_cons_self ..)))
        signatures receipt.projected preparedAt sourceTyped (environment := environment) initial
    rw [emitted]
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedAssignment.preserves bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations shapes budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedAssignment.reflects bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations shapes writes.functionTypes budget (expressions fuel context runtime covers ledger).2
          tailBounds.2⟩
  | bitNotting => intro covered; cases covered
  | @bitNotted fuel scope assignment rest tail code remaining receipt targetType tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bitNot_head index
      (sameSource.trans sourceEq.symm) receipt targetType (sourceEq ▸ assignmentTyped)
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have errors : head.Errors (fun reason token => faults (.semantic reason) token) := by
      show faults (.semantic (.invalidUnaryOperand .bitNot)) head.invalid
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.unary (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨CellAwareInvocationForPostBitNot.preserves bridge transport functions producer head sourceEq errors
        budget tailBounds.1,
      CellAwareInvocationForPostBitNot.reflects bridge transport functions producer head sourceEq errors
        budget tailBounds.2⟩
  | @projectedBitNotted fuel scope assignment rest tail code remaining receipt route tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_bitNot_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have reachedErrors : SourceBitNotAssignmentValid invocation.source context assignment →
        ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
          (initial : protocol.State initialIndex),
          CompatibleProjectedBitNotStatements.Head.ReachedErrors (values := .initial whole.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol head environment
            initial (fun reason token => faults (.semantic reason) token) (registry := receiving) := by
      intro sourceTyped environment initialIndex initial
      cases sourceTyped with
      | intro place _ =>
        exact writes.placeDiagnostics.unary head (.header found parentForm (members _ (List.mem_cons_self ..)))
          signatures preparedAt place initial
    rw [emitted]
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedBitNot.preserves bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations reachedErrors budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedBitNot.reflects bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations reachedErrors writes.functionTypes budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩

include bindings transport registered in
/-- Induction over the accepted initializer items of one actual `for` statement.
The exhausted list enters the loop terminal at the final initializer context. -/
theorem initial_correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    {parentId : StatementId} {statement : StatementNode}
    {allInitial allPost : List ForItemForm} {condition : ExpressionId} {bodyStatements : List StatementId}
    (parentReached : index.Reached (.statement parentId))
    (parentFound : index.compilerSource.lookupStatement? parentId = some statement)
    (parentForm : statement.form = .forLoop allInitial condition allPost bodyStatements)
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {finish : Expr} {expected : TypeSystem.Ty} {test : ExpressionId} {postItems : List ForItemForm}
    {statements : List StatementId} {control : ControlContext} {loopContext : SourceSemantics.Context}
    (terminal : (∃ nativeType, HasType (SourceCoreLocalCell.coreContext finalScope ++ administrative) finish
        nativeType whole.indexed.layouts.definitions) →
      CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge loopContext model index
        producer registry invocation faults administrative finalScope [] test postItems statements expected
        index.result finish budget ∧
      CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge loopContext model index
        producer registry invocation faults administrative finalScope [] test postItems statements expected
        index.result finish budget) :
    ∀ {fuel scope items code}
      (tree : Items index.policy index.compilerSource (.occurrence parentId.occurrence) index.result index.reasonAt
        next finalScope finish fuel scope items code),
      ItemsCovered index.source tree →
      (∀ item ∈ items, item ∈ allInitial ++ allPost) →
      ∀ {context : SourceSemantics.Context},
        context.signatures = whole.compatible.checked.signatures →
        ForItemsHaveType index.source control context items loopContext →
        (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model index
          producer registry invocation faults administrative scope items test postItems statements expected
          index.result code budget ∧
        CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model index
          producer registry invocation faults administrative scope items test postItems statements expected
          index.result code budget := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  intro fuel scope items code tree
  induction tree with
  | @nil fuel scope same accepted =>
    intro _ _ context _ typed native
    subst scope
    cases typed
    exact terminal native
  | @absent fuel scope binder payload rest tail code projected remaining allocated tailIH =>
    intro covered members context signatures typed native
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    cases headTyped with
    | letUninitialized mono _ extended =>
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    have payloadProjected := CellAwareInvocationAcceptedSourceFacts.binder_projected index mono projected
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForInitialAcceptedAllocation.absent_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.1,
      CellAwareInvocationForInitialAcceptedAllocation.absent_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.2⟩
  | @initialized fuel scope binder expression payload rest tail code projected child generated childType
      remaining allocated tailIH =>
    intro covered members context signatures typed native
    obtain ⟨mono, covered⟩ := covered
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    have typedInitializer : ExpressionHasType index.source context expression binder.scheme.body ∧
        BinderExtends index.source.owner context binder middle := by
      cases headTyped with
      | letInitialized initializerTyped _ _ extension => exact ⟨initializerTyped, extension⟩
      | letInitializedGeneralized polymorphic => exact False.elim (polymorphic mono)
    obtain ⟨initializerTyped, extended⟩ := typedInitializer
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    obtain ⟨initializerNode, initializerFound, valueType, initializerTyped⟩ :=
      expression_node sourceUnique initializerTyped
    have payloadEq : payload = child.type := ensure_eq childType
    subst payloadEq
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForInitialAcceptedAllocation.initialized_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).1)
        tailBounds.1,
      CellAwareInvocationForInitialAcceptedAllocation.initialized_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).2)
        tailBounds.2⟩
  | @discard fuel scope expression rest tail child generated remaining tailIH =>
    intro covered members context signatures typed native
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | expression expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialDiscard.preserves bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialDiscard.reflects bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | assigning => intro covered; cases covered
  | @assigned fuel scope assignment operator expression rest tail code remaining receipt targetType tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bare_head index
      (sameSource.trans sourceEq.symm) unique receipt targetType (sourceEq ▸ assignmentTyped) administrative
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have token : AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token)
        operator head.invalid := by
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.operands (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialAssignment.preserves bridge transport functions
          producer unique head receipt.bare (sourceEq ▸ assignmentTyped) writes.extension token budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialAssignment.reflects bridge transport functions
          producer unique head receipt.bare (sourceEq ▸ assignmentTyped) writes.extension token budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @projectedAssigned fuel scope assignment operator expression rest tail code remaining receipt route tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have shapes := fun (sourceTyped : SourceAssignmentHasType invocation.source context assignment operator expression)
        {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
        (initial : protocol.State initialIndex) =>
      writes.placeDiagnostics.assignment head (.header found parentForm (members _ (List.mem_cons_self ..)))
        signatures receipt.projected preparedAt sourceTyped (environment := environment) initial
    rw [emitted]
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedAssignment.preserves bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations shapes budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedAssignment.reflects bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations shapes writes.functionTypes budget (expressions fuel context runtime covers ledger).2
          tailBounds.2⟩
  | bitNotting => intro covered; cases covered
  | @bitNotted fuel scope assignment rest tail code remaining receipt targetType tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bitNot_head index
      (sameSource.trans sourceEq.symm) receipt targetType (sourceEq ▸ assignmentTyped)
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have errors : head.Errors (fun reason token => faults (.semantic reason) token) := by
      show faults (.semantic (.invalidUnaryOperand .bitNot)) head.invalid
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.unary (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨CellAwareInvocationForInitialBitNot.preserves bridge transport functions producer head (sourceEq ▸ assignmentTyped) errors
        budget tailBounds.1,
      CellAwareInvocationForInitialBitNot.reflects bridge transport functions producer head (sourceEq ▸ assignmentTyped) errors
        budget tailBounds.2⟩
  | @projectedBitNotted fuel scope assignment rest tail code remaining receipt route tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_bitNot_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have reachedErrors : SourceBitNotAssignmentValid invocation.source context assignment →
        ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
          (initial : protocol.State initialIndex),
          CompatibleProjectedBitNotStatements.Head.ReachedErrors (values := .initial whole.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol head environment
            initial (fun reason token => faults (.semantic reason) token) (registry := receiving) := by
      intro sourceTyped environment initialIndex initial
      cases sourceTyped with
      | intro place _ =>
        exact writes.placeDiagnostics.unary head (.header found parentForm (members _ (List.mem_cons_self ..)))
          signatures preparedAt place initial
    rw [emitted]
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedBitNot.preserves bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations reachedErrors budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedBitNot.reflects bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations reachedErrors writes.functionTypes budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedForItems
