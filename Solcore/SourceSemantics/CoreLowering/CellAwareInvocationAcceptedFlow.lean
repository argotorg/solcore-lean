import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationEmptyFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationScopedTerminalFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTransferFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationDiscardFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBlockFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationConditionalFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopSequences
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryAcceptedAllocation
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentAcceptedAllocation
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBodyFinish
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBareAssignmentFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBareBitNotFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedBitNotFlow
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.TypedImperativeNative

/-! The actual accepted compiler tree closes the mixed-cell statement flows.
Every child is the action run by the compiler at its original source, scope and
fuel. Fixed-control checker typing supplies the Source facts; expression
meaning is supplied for exactly the expressions the compiler accepted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open AcceptedNamedBodyFlow (Tree)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedSourceFacts (head_form expression_node)

section Coverage
variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
  {reasonAt : ExpressionId → Word}

/-- Compiler branches whose statement flow is closed below. Function-mode
fallthrough is admitted only at a Unit result, and a final bare value only at
the declared result type of its original node. A nonfinal bare value in
function mode has no Source rule and is outside this closure. Bare and
projected assignments and bit-not updates are closed when the compiler view is
the original Source, as for named rows. -/
def Covered (semantic : TypedSource) (expected : TypeSystem.Ty) {mode : Bool} {escaped : Word}
    {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Prop :=
  match tree with
  | .nil => mode = false ∨ expected = .unit
  | .returning .. | .returnUnit .. | .breaking .. | .continuing .. => True
  | @Tree.tailValue _ _ _ _ _ _ _ _ _ _ expression _ _ _ _ _ _ =>
      ∀ node, semantic.lookupExpression? expression = some node → node.type = expected
  | @Tree.initialized _ _ _ _ _ _ _ _ _ _ _ _ binder _ _ _ _ _ _ _ _ _ _ _ remaining _ =>
      binder.scheme.quantified = [] ∧ Covered semantic expected remaining
  | .absent _ _ _ _ remaining _ => Covered semantic expected remaining
  | .assigned _ _ _ remaining _ _ => source = semantic ∧ Covered semantic expected remaining
  | .bitNotted _ _ _ remaining _ _ => source = semantic ∧ Covered semantic expected remaining
  | .projectedAssigned _ _ _ remaining _ _ => source = semantic ∧ Covered semantic expected remaining
  | .projectedBitNotted _ _ _ remaining _ _ => source = semantic ∧ Covered semantic expected remaining
  | .discard _ _ _ _ _ tail => Covered semantic expected tail
  | .valueDiscard _ _ _ _ _ _ tail => mode = false ∧ Covered semantic expected tail
  | .block _ _ inner tail => Covered semantic expected inner ∧ Covered semantic expected tail
  | .conditional _ _ _ _ _ left right tail =>
      Covered semantic expected left ∧ Covered semantic expected right ∧ Covered semantic expected tail
  | .whileLoop _ _ _ _ _ _ inner tail => Covered semantic expected inner ∧ Covered semantic expected tail
  | _ => False

end Coverage

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

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

section Validity
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {budget : Nat}

/-- Runtime validity of the fixed Source context is part of every flow port. -/
theorem preserves_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope mode statements expected type code budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode statements expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

theorem reflects_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope mode statements expected type code budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode statements expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

end Validity

/-- Accepted-expression meaning for every child the compiler lowered, at every
compiler fuel. This is the only expression input of the statement closure. -/
def Expressions (budget : Nat) : Prop :=
  ∀ fuel context, Dynamic.SourceRuntimeValid program context index.source →
    invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
    CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index
      registry invocation (children index fuel) faults budget ∧
    CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index
      registry invocation (children index fuel) faults budget

include bindings transport registered in
/-- Induction over the actual compiler tree. Each covered branch applies its
existing flow theorem to the compiler's read, lowered children and allocation
receipt; nested statement lists inherit reachability, checker typing and native
typing from the enclosing compiled code. -/
theorem correct (budget : Nat)
    (expressions : Expressions (attachment := attachment) (receiving := receiving) (functions := functions)
      bridge index registry invocation faults budget)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (operands : ∀ site root operator, AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator (index.invalidOperand site root operator))
    (unary : ∀ site root, faults (.semantic (.invalidUnaryOperand .bitNot)) (index.invalidUnary site root))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities)
    (functionTypes : CompatiblePayload.FunctionRuntimeViews functions)
    (placeDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol invocation.source
      index.invalidProjection index.missingDefault receiving (fun reason token => faults (.semantic reason) token))
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {expected : TypeSystem.Ty} :
    ∀ {mode escaped fuel scope statements code}
      (tree : Tree index.policy index.compilerSource index.result index.reasonAt mode escaped fuel scope statements code),
      Covered index.source expected tree →
      (∀ id ∈ statements, index.Reached (.statement id)) →
      ∀ {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts},
        control.returnType = expected →
        context.signatures = whole.compatible.checked.signatures →
        StatementsHaveType index.source control context statements final facts →
        (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope mode statements expected index.result code budget ∧
        CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope mode statements expected index.result code budget := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  intro mode escaped fuel scope statements code tree
  induction tree with
  | nil =>
    intro allowed _ control context final facts _ _ _ _
    exact ⟨fun size _ => CellAwareInvocationEmptyFlow.preserves bridge context model index producer
        registry invocation faults administrative _ _ expected index.result allowed size,
      fun size _ => CellAwareInvocationEmptyFlow.reflects bridge context model index producer
        registry invocation faults administrative _ _ expected index.result allowed size⟩
  | @returning mode escaped fuel scope id rest node stored expression read form statementType child generated childType =>
    intro _ reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, _restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | returnValue valueTyped =>
    obtain ⟨expressionNode, expressionFound, valueType, expressionTyped⟩ :=
      expression_node sourceUnique valueTyped
    rw [result] at valueType
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode (id :: rest) :=
      .returning rest (sourceEq ▸ lookupStatement?_sound statementFound) form
    rw [ensure_eq childType, ← valueType]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.preserves bridge producer unique head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).1),
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.reflects bridge producer head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).2)⟩
  | @returnUnit mode escaped fuel scope id rest node stored read form statementType unitType =>
    intro _ reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, _restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | returnUnit unitResult =>
    have resultUnit : index.result = .unit := (ensure_eq statementType).trans (ensure_eq unitType).symm
    rw [← result, unitResult, resultUnit]
    have found := sourceEq ▸ statementFound
    exact ⟨fun size _ => CellAwareInvocationScopedTerminalFlow.unit_preserves bridge producer
        (fun _ _ => CompatiblePayload.ValueRep.unit) found form unique size,
      fun size _ => CellAwareInvocationScopedTerminalFlow.unit_reflects bridge producer
        (fun _ _ => CompatiblePayload.ValueRep.unit) found form size⟩
  | @initialized mode escaped fuel scope id rest node stored binder initializer payload tail code
      read form statementType projected child generated childType remaining allocated tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨mono, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    have typedInitializer : ExpressionHasType index.source context initializer binder.scheme.body ∧
        BinderExtends index.source.owner context binder middle := by
      cases formTyped with
      | letInitialized initializerTyped _ extension => exact ⟨initializerTyped, extension⟩
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
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result nextSignatures restTyped ⟨_, tailNative⟩
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationOrdinaryAcceptedAllocation.preserves bridge bindings model
          index producer registered registry invocation faults headReached read form mono extended childType
          allocated sourceEq initializerFound valueType initializerTyped generated budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationOrdinaryAcceptedAllocation.reflects bridge bindings model
          index producer registered registry invocation faults headReached read form mono extended childType
          allocated sourceEq initializerFound valueType initializerTyped generated budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @absent mode escaped fuel scope id rest node stored binder payload tail code
      read form statementType projected remaining allocated tailIH =>
    intro covered reached control context final facts result signatures typed native
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | letUninitialized mono extended =>
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    have payloadProjected := CellAwareInvocationAcceptedSourceFacts.binder_projected index mono projected
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result nextSignatures restTyped ⟨_, tailNative⟩
    exact ⟨CellAwareInvocationAbsentAcceptedAllocation.preserves bridge bindings model index producer registered
        registry invocation faults headReached read form mono extended allocated sourceEq payloadProjected
        budget tailBounds.1,
      CellAwareInvocationAbsentAcceptedAllocation.reflects bridge bindings model index producer registered
        registry invocation faults headReached read form mono extended allocated sourceEq payloadProjected
        budget tailBounds.2⟩
  | assigning => intro covered; cases covered
  | @assigned mode escaped fuel scope id rest node stored assignment operator expression tail code
      read form statementType remaining receipt targetType tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignValue assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bare_head index
      (sameSource.trans sourceEq.symm) unique receipt targetType (sourceEq ▸ assignmentTyped) administrative
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have token : AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token)
        operator head.invalid := by
      rw [invalid]
      exact operands _ _ _
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationBareAssignmentFlow.preserves bridge transport functions
          producer sourceEq unique (sourceEq ▸ statementFound) form head receipt.bare extension token budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationBareAssignmentFlow.reflects bridge transport functions
          producer sourceEq unique (sourceEq ▸ statementFound) form head receipt.bare extension token budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @projectedAssigned mode escaped fuel scope id rest node stored assignment operator expression tail code
      read form statementType remaining receipt route tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignValue assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have found := sourceEq ▸ statementFound
    have shapes := fun (sourceTyped : SourceAssignmentHasType invocation.source context assignment operator expression)
        {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
        (initial : protocol.State initialIndex) =>
      placeDiagnostics.assignment head (.statement found form) signatures receipt.projected preparedAt sourceTyped
        (environment := environment) initial
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedAssignmentFlow.preserves bridge transport functions
          producer sourceEq unique found form head receipt.projected extension faithful observations shapes budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedAssignmentFlow.reflects bridge transport functions
          producer sourceEq unique found form head receipt.projected extension faithful observations shapes
          functionTypes budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | bitNotting => intro covered; cases covered
  | @bitNotted mode escaped fuel scope id rest node stored assignment tail code
      read form statementType remaining receipt targetType tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bitNot_head index
      (sameSource.trans sourceEq.symm) receipt targetType (sourceEq ▸ assignmentTyped)
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have errors : head.Errors (fun reason token => faults (.semantic reason) token) := by
      show faults (.semantic (.invalidUnaryOperand .bitNot)) head.invalid
      rw [invalid]
      exact unary _ _
    rw [emitted]
    exact ⟨CellAwareInvocationBareBitNotFlow.preserves bridge transport functions producer head sourceEq unique
        (sourceEq ▸ statementFound) form errors budget tailBounds.1,
      CellAwareInvocationBareBitNotFlow.reflects bridge transport functions producer head sourceEq unique
        (sourceEq ▸ statementFound) form errors budget tailBounds.2⟩
  | @projectedBitNotted mode escaped fuel scope id rest node stored assignment tail code
      read form statementType remaining receipt route tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_bitNot_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have found := sourceEq ▸ statementFound
    have reachedErrors : SourceBitNotAssignmentValid invocation.source context assignment →
        ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
          (initial : protocol.State initialIndex),
          CompatibleProjectedBitNotStatements.Head.ReachedErrors (values := .initial whole.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol head environment
            initial (fun reason token => faults (.semantic reason) token) (registry := receiving) := by
      intro sourceTyped environment initialIndex initial
      cases sourceTyped with
      | intro place _ => exact placeDiagnostics.unary head (.statement found form) signatures preparedAt place initial
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedBitNotFlow.preserves bridge transport functions
          producer sourceEq unique found form head receipt.projected extension faithful observations reachedErrors
          budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedBitNotFlow.reflects bridge transport functions
          producer sourceEq unique found form head receipt.projected extension faithful observations reachedErrors
          functionTypes budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @discard mode escaped fuel scope id rest node stored expression tail read form child generated statementType remaining tailIH =>
    intro covered reached control context final facts result signatures typed native
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | expressionDiscard expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.preserves bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inl rfl) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.reflects bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inl rfl) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @tailValue escaped fuel scope id node stored expression read form child generated statementType childType =>
    intro covered reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, _restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | expressionValue expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    have valueType : expressionNode.type = expected := covered expressionNode expressionFound
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression true [id] :=
      .tail (sourceEq ▸ lookupStatement?_sound statementFound) form
    rw [ensure_eq childType, ← valueType]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.preserves bridge producer unique head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).1),
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.reflects bridge producer head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).2)⟩
  | @valueDiscard mode escaped fuel scope id rest node stored expression tail read form notTail child generated statementType remaining tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨modeFalse, covered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | expressionValue expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.preserves bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inr modeFalse) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.reflects bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inr modeFalse) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @block mode escaped fuel scope id rest node stored statements innerCode tail read form inner remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨innerCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | block innerTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, innerNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    have innerReached : ∀ other ∈ statements, index.Reached (.statement other) := fun other member =>
      index.statement_child headReached read (by rw [form]; simp [StatementForm.references, member])
    have innerBounds := innerIH innerCovered innerReached result signatures innerTyped ⟨_, innerNative⟩
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    exact ⟨CellAwareInvocationBlockFlow.preserves bridge context model index producer registry invocation faults
        administrative scope mode expected index.result sourceEq unique (sourceEq ▸ statementFound) form budget
        innerBounds.1 tailBounds.1,
      CellAwareInvocationBlockFlow.reflects bridge context model index producer registry invocation faults
        administrative scope mode expected index.result sourceEq unique (sourceEq ▸ statementFound) form budget
        innerBounds.2 tailBounds.2⟩
  | @conditional mode escaped fuel scope id rest node stored condition thenBody elseBody thenCode elseCode tail
      read form child generated conditionType left right remaining leftIH rightIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨leftCovered, rightCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    cases child with
    | mk childType childCode =>
    have boolType := ensure_eq conditionType
    dsimp only at boolType
    subst boolType
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, branchNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    obtain ⟨⟨_, thenNative⟩, ⟨_, elseNative⟩⟩ := TypedLexicalWhile.Native.conditional_children branchNative
    have thenReached : ∀ other ∈ thenBody, index.Reached (.statement other) := fun other member =>
      index.statement_child headReached read (by rw [form]; simp [StatementForm.references, member])
    have elseReached : ∀ other ∈ elseBody.getD [], index.Reached (.statement other) := fun other member =>
      index.statement_child headReached read (by rw [form]; simp [StatementForm.references, member])
    have tailReached : ∀ other ∈ rest, index.Reached (.statement other) := fun other member =>
      reached other (List.mem_cons_of_mem _ member)
    rw [form] at formTyped
    have branches : ∃ conditionTyped : ExpressionHasType index.source context condition .bool,
        (∃ thenFinal thenFacts, StatementsHaveType index.source control context thenBody thenFinal thenFacts) ∧
        (∃ elseFinal elseFacts, StatementsHaveType index.source control context (elseBody.getD []) elseFinal elseFacts) ∧
        middle = context := by
      cases formTyped with
      | ifWithoutElse conditionTyped thenTyped => exact ⟨conditionTyped, ⟨_, _, thenTyped⟩, ⟨_, _, .nil _ _⟩, rfl⟩
      | ifWithElse conditionTyped thenTyped elseTyped => exact ⟨conditionTyped, ⟨_, _, thenTyped⟩, ⟨_, _, elseTyped⟩, rfl⟩
    obtain ⟨conditionTyped, ⟨_, _, thenTyped⟩, ⟨_, _, elseTyped⟩, sameMiddle⟩ := branches
    subst middle
    obtain ⟨conditionNode, conditionFound, nodeType, conditionTyped⟩ := expression_node sourceUnique conditionTyped
    have leftBounds := leftIH leftCovered thenReached result signatures thenTyped ⟨_, thenNative⟩
    have rightBounds := rightIH rightCovered elseReached result signatures elseTyped ⟨_, elseNative⟩
    have tailBounds := tailIH tailCovered tailReached result signatures restTyped ⟨_, tailNative⟩
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationConditionalFlow.preserves bridge context model index producer
          registry invocation faults administrative scope expected index.result
          (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
          (sourceEq ▸ conditionFound) nodeType (sourceEq ▸ conditionTyped) generated sourceEq unique
          (sourceEq ▸ statementFound) form budget (expressions fuel context runtime covers ledger).1
          leftBounds.1 rightBounds.1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationConditionalFlow.reflects bridge context model index producer
          registry invocation faults administrative scope expected index.result
          (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
          (sourceEq ▸ conditionFound) nodeType (sourceEq ▸ conditionTyped) generated sourceEq unique
          (sourceEq ▸ statementFound) form budget (expressions fuel context runtime covers ledger).2
          leftBounds.2 rightBounds.2 tailBounds.2⟩
  | matching => intro covered; cases covered
  | matched => intro covered; cases covered
  | @whileLoop mode escaped fuel scope id rest node stored condition body loopCode tail read form statementType
      child generated conditionType inner remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨innerCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    cases child with
    | mk childType childCode =>
    have boolType := ensure_eq conditionType
    dsimp only at boolType
    subst boolType
    rw [form] at formTyped
    cases formTyped with
    | whileLoop conditionTyped bodyTyped =>
    obtain ⟨conditionNode, conditionFound, nodeType, conditionTyped⟩ := expression_node sourceUnique conditionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, loopNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    obtain ⟨⟨_, bodyNative⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopNative
    have innerReached : ∀ other ∈ body, index.Reached (.statement other) := fun other member =>
      index.statement_child headReached read (by rw [form]; simp [StatementForm.references, member])
    have innerBounds := innerIH innerCovered innerReached (control := control.enterLoop) result signatures bodyTyped
      ⟨_, bodyNative⟩
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    refine ⟨?_, ?_⟩
    · intro size within mapping world actualContext environment canonical actual before store embedding
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready finalContext outcome after trace
      exact CellAwareInvocationLoopSequences.preserves bridge model producer transport
        (fun represented => CompatibleExpressionPrimitives.bool_fields represented) sourceEq
        (expressions fuel context runtime covers sameLedger).1 (sourceEq ▸ conditionFound) nodeType
        (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.1 unique (sourceEq ▸ statementFound) form
        tailBounds.1 within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace
    · intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed
      exact CellAwareInvocationLoopSequences.reflects bridge model producer transport
        (fun represented => CompatibleExpressionPrimitives.bool_fields represented) sourceEq
        (expressions fuel context runtime covers sameLedger).2 (sourceEq ▸ conditionFound) nodeType
        (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.2 (sourceEq ▸ statementFound) form
        tailBounds.2 within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed
  | @breaking mode escaped fuel scope id rest node stored read form statementType =>
    intro _ reached control context final facts _ _ _ _
    have found := sourceEq ▸ index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    exact ⟨fun size _ => CellAwareInvocationTransferFlow.breaking_preserves bridge context model index producer
        registry invocation faults administrative scope mode expected index.result unique found form size,
      fun size _ => CellAwareInvocationTransferFlow.breaking_reflects bridge context model index producer
        registry invocation faults administrative scope mode expected index.result found form size⟩
  | @continuing mode escaped fuel scope id rest node stored read form statementType =>
    intro _ reached control context final facts _ _ _ _
    have found := sourceEq ▸ index.statement_read_reached (reached id (List.mem_cons_self ..)) read
    exact ⟨fun size _ => CellAwareInvocationTransferFlow.continuing_preserves bridge context model index producer
        registry invocation faults administrative scope mode expected index.result unique found form size,
      fun size _ => CellAwareInvocationTransferFlow.continuing_reflects bridge context model index producer
        registry invocation faults administrative scope mode expected index.result found form size⟩
  | forLoop => intro covered; cases covered
  | forBoundary => intro covered; cases covered
  | boundary => intro covered; cases covered

include bindings transport registered in
/-- The complete accepted body of an actual named or contextual invocation:
its compiler tree, footer and native result. Source executions of the original
statements are related in both directions at the actual reached heap. -/
theorem body_preserves (budget : Nat)
    (expressions : Expressions (attachment := attachment) (receiving := receiving) (functions := functions)
      bridge index registry invocation faults budget)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (operands : ∀ site root operator, AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator (index.invalidOperand site root operator))
    (unary : ∀ site root, faults (.semantic (.invalidUnaryOperand .bitNot)) (index.invalidUnary site root))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities)
    (functionTypes : CompatiblePayload.FunctionRuntimeViews functions)
    (placeDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol invocation.source
      index.invalidProjection index.missingDefault receiving (fun reason token => faults (.semantic reason) token))
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected body.tree)
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
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  have flowNative : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative)
      body.flow nativeType whole.indexed.layouts.definitions := by
    obtain ⟨_, native⟩ := native
    rw [body.emitted] at native
    exact TypedLexicalWhile.Native.finished_flow native
  have bound := (correct bridge bindings transport index producer registered registry invocation faults
    administrative budget expressions extension operands unary faithful observations functionTypes placeDiagnostics
    sourceEq unique body.tree covered (fun _ member => index.body_root member)
    result signatures sourceTyped flowNative).1
  intro size within
  rw [body.emitted]
  exact CellAwareInvocationBodyFinish.preserves bridge producer bound sourceEq sourceTyped depth projection
    index.fellThrough index.escaped within

include bindings transport registered in
/-- Native completion of the same complete accepted body reconstructs an
original Source execution, its body result and the reached heap. -/
theorem body_reflects (budget : Nat)
    (expressions : Expressions (attachment := attachment) (receiving := receiving) (functions := functions)
      bridge index registry invocation faults budget)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (operands : ∀ site root operator, AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator (index.invalidOperand site root operator))
    (unary : ∀ site root, faults (.semantic (.invalidUnaryOperand .bitNot)) (index.invalidUnary site root))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities)
    (functionTypes : CompatiblePayload.FunctionRuntimeViews functions)
    (placeDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol invocation.source
      index.invalidProjection index.missingDefault receiving (fun reason token => faults (.semantic reason) token))
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected body.tree)
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
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  have flowNative : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative)
      body.flow nativeType whole.indexed.layouts.definitions := by
    obtain ⟨_, native⟩ := native
    rw [body.emitted] at native
    exact TypedLexicalWhile.Native.finished_flow native
  have bound := (correct bridge bindings transport index producer registered registry invocation faults
    administrative budget expressions extension operands unary faithful observations functionTypes placeDiagnostics
    sourceEq unique body.tree covered (fun _ member => index.body_root member)
    result signatures sourceTyped flowNative).2
  intro size within
  rw [body.emitted]
  exact CellAwareInvocationBodyFinish.reflects bridge producer bound sourceEq sourceTyped depth projection
    index.fellThrough index.escaped within

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
