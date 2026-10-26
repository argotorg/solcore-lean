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
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedForItems
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialTerminal
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForSequences
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBareAssignmentFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBareBitNotFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedBitNotFlow
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.TypedImperativeNative
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMatches
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNative
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedAcceptedAllocation

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

/-- A generalized declaration's initializer is a direct lambda without
requirements or coercions. -/
def LambdaInitializer (semantic : TypedSource) (expression : ExpressionId) : Prop :=
  ∀ node, semantic.lookupExpression? expression = some node →
    (∃ parameters result body, node.form = .lambda parameters result body) ∧
      node.requirements = [] ∧ node.coercions = []

/-- Compiler branches whose statement flow is closed below. Function-mode
fallthrough is admitted only at a Unit result, and a final bare value only at
the declared result type of its original node. A nonfinal bare value in
function mode has no Source rule and is outside this closure. Bare and
projected assignments and bit-not updates are closed when the compiler view is
the original Source, as for named rows. A match receipt is closed under the
same view when its compilation context is `admitted`, and a generalized
declaration when its inputs are `generalized` and its initializer is a direct
lambda. -/
def Covered (semantic : TypedSource) (expected : TypeSystem.Ty)
    (admitted : SourceCoreCompatibleDataMatches.Context → Prop) (generalized : Prop)
    {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Prop :=
  match tree with
  | .nil => mode = false ∨ expected = .unit
  | .returning .. | .returnUnit .. | .breaking .. | .continuing .. => True
  | @Tree.tailValue _ _ _ _ _ _ _ _ _ _ expression _ _ _ _ _ _ =>
      ∀ node, semantic.lookupExpression? expression = some node → node.type = expected
  | @Tree.initialized _ _ _ _ _ _ _ _ _ _ _ _ binder expression _ _ _ _ _ _ _ _ _ _ remaining _ =>
      (binder.scheme.quantified = [] ∨ generalized ∧ LambdaInitializer semantic expression) ∧
        Covered semantic expected admitted generalized remaining
  | .absent _ _ _ _ remaining _ => Covered semantic expected admitted generalized remaining
  | .assigned _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .bitNotted _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .projectedAssigned _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .projectedBitNotted _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .discard _ _ _ _ _ tail => Covered semantic expected admitted generalized tail
  | .valueDiscard _ _ _ _ _ _ tail => mode = false ∧ Covered semantic expected admitted generalized tail
  | .block _ _ inner tail =>
      Covered semantic expected admitted generalized inner ∧ Covered semantic expected admitted generalized tail
  | .conditional _ _ _ _ _ left right tail =>
      Covered semantic expected admitted generalized left ∧
        Covered semantic expected admitted generalized right ∧ Covered semantic expected admitted generalized tail
  | @Tree.matched _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ compilation _ _ _ branches tail =>
      admitted compilation ∧ source = semantic ∧
        (∀ request member, Covered semantic expected admitted generalized (branches request member)) ∧
        Covered semantic expected admitted generalized tail
  | .whileLoop _ _ _ _ _ _ inner tail =>
      Covered semantic expected admitted generalized inner ∧ Covered semantic expected admitted generalized tail
  | .forLoop _ _ _ _ _ _ initial inner after tail =>
      CellAwareInvocationAcceptedForItems.ItemsCovered semantic initial ∧
        Covered semantic expected admitted generalized inner ∧
        CellAwareInvocationAcceptedForItems.ItemsCovered semantic after ∧
        Covered semantic expected admitted generalized tail
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

include bindings transport registered in
/-- Induction over the actual compiler tree. Each covered branch applies its
existing flow theorem to the compiler's read, lowered children and allocation
receipt; nested statement lists inherit reachability, checker typing and native
typing from the enclosing compiled code. -/
theorem correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {expected : TypeSystem.Ty} :
    ∀ {mode escaped fuel scope statements code}
      (tree : Tree index.policy index.compilerSource index.result index.reasonAt mode escaped fuel scope statements code),
      Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
        (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) tree →
      (∀ id ∈ statements, index.Site (.statement id)) →
      ∀ {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts},
        control.returnType = expected →
        context.signatures = whole.compatible.checked.signatures →
        StatementsHaveType index.source control context statements final facts →
        (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope mode statements expected index.result code budget ∧
        CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope mode statements expected index.result code budget ∧
        CellAwareInvocationAcceptedNative.WordFailure (SourceCoreLocalCell.coreContext scope ++ administrative) code
          whole.indexed.layouts.definitions := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  have catalog := CellAwareInvocationAcceptedMatches.catalog artifact checked
  intro mode escaped fuel scope statements code tree
  induction tree with
  | nil =>
    intro allowed _ control context final facts _ _ _ _
    exact ⟨fun size _ => CellAwareInvocationEmptyFlow.preserves bridge context model index producer
        registry invocation faults administrative _ _ expected index.result allowed size,
      fun size _ => CellAwareInvocationEmptyFlow.reflects bridge context model index producer
        registry invocation faults administrative _ _ expected index.result allowed size,
      CellAwareInvocationAcceptedNative.fallthrough_word _⟩
  | @returning mode escaped fuel scope id rest node stored expression read form statementType child generated childType =>
    intro _ reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
          ((expressions fuel context runtime covers ledger).2),
      CellAwareInvocationAcceptedNative.returnValue_word _ _⟩
  | @returnUnit mode escaped fuel scope id rest node stored read form statementType unitType =>
    intro _ reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
        (fun _ _ => CompatiblePayload.ValueRep.unit) found form size,
      CellAwareInvocationAcceptedNative.returned_word _⟩
  | @initialized mode escaped fuel scope id rest node stored binder initializer payload tail code
      read form statementType projected child generated childType remaining allocated tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨shape, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    have payloadEq : payload = child.type := ensure_eq childType
    subst payloadEq
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
    obtain ⟨nativeType, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ native)
    by_cases mono : binder.scheme.quantified = []
    · have typedInitializer : ExpressionHasType index.source context initializer binder.scheme.body ∧
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
      have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
        result nextSignatures restTyped ⟨_, tailNative⟩
      exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
          fun runtime covers ledger => CellAwareInvocationOrdinaryAcceptedAllocation.preserves bridge bindings model
            index producer registered registry invocation faults headReached.reached read form mono extended
            childType allocated sourceEq initializerFound valueType initializerTyped generated budget
            (expressions fuel context runtime covers ledger).1 tailBounds.1,
        reflects_of_valid bridge index producer registry invocation faults administrative
          fun runtime covers ledger => CellAwareInvocationOrdinaryAcceptedAllocation.reflects bridge bindings model
            index producer registered registry invocation faults headReached.reached read form mono extended
            childType allocated sourceEq initializerFound valueType initializerTyped generated budget
            (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
        by
          intro _ typed
          exact tailBounds.2.2 (TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ typed))⟩
    · obtain ⟨generalized, lambdaShape⟩ := shape.resolve_left mono
      have typedInitializer : ExpressionHasType index.source (localSchemeInitializerContext context binder)
            initializer binder.scheme.body ∧ BinderExtends index.source.owner context binder middle := by
        cases formTyped with
        | letInitialized _ monomorphic _ => exact False.elim (mono monomorphic)
        | letInitializedGeneralized _ _ _ initializerTyped extension => exact ⟨initializerTyped, extension⟩
      obtain ⟨initializerTyped, extended⟩ := typedInitializer
      have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
        cases extended
        exact signatures
      obtain ⟨initializerNode, initializerFound, valueType, _⟩ := expression_node sourceUnique initializerTyped
      obtain ⟨⟨parameters, lambdaResult, lambdaBody, initializerForm⟩, requirements, coercions⟩ :=
        lambdaShape initializerNode initializerFound
      have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
        result nextSignatures restTyped ⟨_, tailNative⟩
      have word : CellAwareInvocationAcceptedNative.WordFailure (SourceCoreLocalCell.coreContext scope ++ administrative)
          code whole.indexed.layouts.definitions := by
        intro _ typed
        exact tailBounds.2.2 (TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ typed))
      obtain ⟨success, nativeEq⟩ := word native
      subst nativeEq
      rw [emitted] at native
      have nativeTyped := CellAwareInvocationAcceptedNative.initialized_initializer allocation annotation same native
      obtain ⟨attachmentEq, entry, issuer⟩ := generalized
      subst attachmentEq
      refine ⟨?_, ?_, word⟩
      · intro size within mapping world actualContext environment canonical actual before store embedding
          environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
          initial admitted authority physical owner sameLocation ready finalContext outcome after trace
        obtain ⟨_, declaration, ordinary⟩ := SourceLetDeclarationFacts.of_lookup physical.ownership statementFound form
        exact CellAwareInvocationGeneralizedAcceptedAllocation.preserves bridge bindings model index producer
          registered registry invocation faults (artifact := artifact) (checked := checked) (entry := entry)
          (site := headReached) (read := read) (form := form) (projected := projected) (generated := generated)
          (issuer := issuer fuel scope initializer) (declaration := declaration) (polymorphic := mono)
          (extended := extended) (ordinary := ordinary) (nativeTyped := nativeTyped) (childType := childType)
          (allocated := allocated) (sourceEq := sourceEq) budget tailBounds.1 size within environments heaps
          locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner
          sameLocation ready trace
      · intro size within mapping world actualContext environment canonical actual before store embedding value
          finalStore environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
          initial admitted authority physical owner sameLocation ready completed
        obtain ⟨_, declaration, ordinary⟩ := SourceLetDeclarationFacts.of_lookup physical.ownership statementFound form
        exact CellAwareInvocationGeneralizedAcceptedAllocation.reflects bridge bindings model index producer
          registered registry invocation faults (artifact := artifact) (checked := checked) (entry := entry)
          (site := headReached) (read := read) (form := form) (projected := projected) (generated := generated)
          (issuer := issuer fuel scope initializer) (declaration := declaration) (polymorphic := mono)
          (extended := extended) (ordinary := ordinary) (nativeTyped := nativeTyped) (childType := childType)
          (allocated := allocated) (sourceEq := sourceEq) (initializerFound := initializerFound)
          (initializerForm := initializerForm) (valueType := valueType) (requirements := requirements)
          (coercions := coercions) budget tailBounds.2.1 size within environments heaps locals agrees actualTyped
          runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready completed
  | @absent mode escaped fuel scope id rest node stored binder payload tail code
      read form statementType projected remaining allocated tailIH =>
    intro covered reached control context final facts result signatures typed native
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
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
        registry invocation faults headReached.reached read form mono extended allocated sourceEq payloadProjected
        budget tailBounds.1,
      CellAwareInvocationAbsentAcceptedAllocation.reflects bridge bindings model index producer registered
        registry invocation faults headReached.reached read form mono extended allocated sourceEq payloadProjected
        budget tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ typed))⟩
  | assigning => intro covered; cases covered
  | @assigned mode escaped fuel scope id rest node stored assignment operator expression tail code
      read form statementType remaining receipt targetType tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
      exact writes.operands _ _ _
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationBareAssignmentFlow.preserves bridge transport functions
          producer sourceEq unique (sourceEq ▸ statementFound) form head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationBareAssignmentFlow.reflects bridge transport functions
          producer sourceEq unique (sourceEq ▸ statementFound) form head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | @projectedAssigned mode escaped fuel scope id rest node stored assignment operator expression tail code
      read form statementType remaining receipt route tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
      writes.placeDiagnostics.assignment head (.statement found form) signatures receipt.projected preparedAt sourceTyped
        (environment := environment) initial
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedAssignmentFlow.preserves bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations shapes budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedAssignmentFlow.reflects bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations shapes
          writes.functionTypes budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | bitNotting => intro covered; cases covered
  | @bitNotted mode escaped fuel scope id rest node stored assignment tail code
      read form statementType remaining receipt targetType tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
      exact writes.unary _ _
    rw [emitted]
    exact ⟨CellAwareInvocationBareBitNotFlow.preserves bridge transport functions producer head sourceEq unique
        (sourceEq ▸ statementFound) form errors budget tailBounds.1,
      CellAwareInvocationBareBitNotFlow.reflects bridge transport functions producer head sourceEq unique
        (sourceEq ▸ statementFound) form errors budget tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | @projectedBitNotted mode escaped fuel scope id rest node stored assignment tail code
      read form statementType remaining receipt route tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
      | intro place _ => exact writes.placeDiagnostics.unary head (.statement found form) signatures preparedAt place initial
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedBitNotFlow.preserves bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations reachedErrors
          budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedBitNotFlow.reflects bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations reachedErrors
          writes.functionTypes budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | @discard mode escaped fuel scope id rest node stored expression tail read form child generated statementType remaining tailIH =>
    intro covered reached control context final facts result signatures typed native
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
          generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (CellAwareInvocationAcceptedNative.discard_tail typed)⟩
  | @tailValue escaped fuel scope id node stored expression read form child generated statementType childType =>
    intro covered reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
          ((expressions fuel context runtime covers ledger).2),
      CellAwareInvocationAcceptedNative.returnValue_word _ _⟩
  | @valueDiscard mode escaped fuel scope id rest node stored expression tail read form notTail child generated statementType remaining tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨modeFalse, covered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
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
          generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (CellAwareInvocationAcceptedNative.discard_tail typed)⟩
  | @block mode escaped fuel scope id rest node stored statements innerCode tail read form inner remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨innerCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | block innerTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, innerNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    have innerReached : ∀ other ∈ statements, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have innerBounds := innerIH innerCovered innerReached result signatures innerTyped ⟨_, innerNative⟩
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    exact ⟨CellAwareInvocationBlockFlow.preserves bridge context model index producer registry invocation faults
        administrative scope mode expected index.result sourceEq unique (sourceEq ▸ statementFound) form budget
        innerBounds.1 tailBounds.1,
      CellAwareInvocationBlockFlow.reflects bridge context model index producer registry invocation faults
        administrative scope mode expected index.result sourceEq unique (sourceEq ▸ statementFound) form budget
        innerBounds.2.1 tailBounds.2.1,
      CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
  | @conditional mode escaped fuel scope id rest node stored condition thenBody elseBody thenCode elseCode tail
      read form child generated conditionType left right remaining leftIH rightIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨leftCovered, rightCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    cases child with
    | mk childType childCode =>
    have boolType := ensure_eq conditionType
    dsimp only at boolType
    subst boolType
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, branchNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    obtain ⟨⟨_, thenNative⟩, ⟨_, elseNative⟩⟩ := TypedLexicalWhile.Native.conditional_children branchNative
    have thenReached : ∀ other ∈ thenBody, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have elseReached : ∀ other ∈ elseBody.getD [], index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have tailReached : ∀ other ∈ rest, index.Site (.statement other) := fun other member =>
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
          leftBounds.2.1 rightBounds.2.1 tailBounds.2.1,
      CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
  | matching => intro covered; cases covered
  | @matched mode escaped fuel scope id rest node stored resolution matchedCode tail compilation
      read form receipt branches remaining branchIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨admitted, sameSource, branchesCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    have sameMiddle : middle = context := by cases formTyped <;> rfl
    subst middle
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, matchedNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have branchReached : ∀ request (member : request ∈ receipt.requests),
        ∀ other ∈ request.statements, index.Site (.statement other) := by
      intro request member other otherMember
      apply headReached.statement_source_child statementFound
      rw [form]
      simp only [StatementForm.references, MatchResolution.references]
      rcases receipt.original request member with ⟨arm, armMember, same⟩ | same
      · exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨arm, armMember, List.mem_map.mpr ⟨other, same ▸ otherMember, rfl⟩⟩))
      · rw [same, Option.getD_some]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨other, otherMember, rfl⟩)
    have matchBounds := CellAwareInvocationAcceptedMatches.correct bridge bindings index producer registered
      registry invocation faults administrative budget expressions writes catalog sourceEq unique headReached.reached
      read form receipt admitted sameSource
      (by
        intro request member _ _ _ _ childResult childSignatures childTyped childNative
        have branchBounds := branchIH request member (branchesCovered request member) (branchReached request member)
          childResult childSignatures childTyped childNative
        exact ⟨branchBounds.1, branchBounds.2.1⟩)
      result signatures typed ⟨_, matchedNative⟩ ⟨tailBounds.1, tailBounds.2.1⟩
    exact ⟨matchBounds.1, matchBounds.2, CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
  | @whileLoop mode escaped fuel scope id rest node stored condition body loopCode tail read form statementType
      child generated conditionType inner remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨innerCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
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
    have innerReached : ∀ other ∈ body, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have innerBounds := innerIH innerCovered innerReached (control := control.enterLoop) result signatures bodyTyped
      ⟨_, bodyNative⟩
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    refine ⟨?_, ?_, CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
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
        (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.2.1 (sourceEq ▸ statementFound) form
        tailBounds.2.1 within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed
  | @breaking mode escaped fuel scope id rest node stored read form statementType =>
    intro _ reached control context final facts _ _ _ _
    have found := sourceEq ▸ index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    exact ⟨fun size _ => CellAwareInvocationTransferFlow.breaking_preserves bridge context model index producer
        registry invocation faults administrative scope mode expected index.result unique found form size,
      fun size _ => CellAwareInvocationTransferFlow.breaking_reflects bridge context model index producer
        registry invocation faults administrative scope mode expected index.result found form size,
      CellAwareInvocationAcceptedNative.breaking_word _⟩
  | @continuing mode escaped fuel scope id rest node stored read form statementType =>
    intro _ reached control context final facts _ _ _ _
    have found := sourceEq ▸ index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    exact ⟨fun size _ => CellAwareInvocationTransferFlow.continuing_preserves bridge context model index producer
        registry invocation faults administrative scope mode expected index.result unique found form size,
      fun size _ => CellAwareInvocationTransferFlow.continuing_reflects bridge context model index producer
        registry invocation faults administrative scope mode expected index.result found form size,
      CellAwareInvocationAcceptedNative.continuing_word _⟩
  | @forLoop mode escaped fuel scope id rest node stored initializer condition post body loopScope postScope
      loopCode postCode initialCode tail read form statementType child generated conditionType initial inner after
      remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨initialCovered, innerCovered, afterCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    have compilerFound := CellAwareInvocationAcceptedSourceFacts.compiler_read index read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    cases child with
    | mk childType childCode =>
    have boolType := ensure_eq conditionType
    dsimp only at boolType
    subst boolType
    rw [form] at formTyped
    cases formTyped with
    | @forLoop _ _ _ _ loopContext _ _ _ initialTyped conditionTyped bodyTyped postTyped =>
    have loopSignatures := CellAwareInvocationAcceptedSourceFacts.items_signatures initialTyped signatures
    obtain ⟨conditionNode, conditionFound, nodeType, conditionTyped⟩ := expression_node sourceUnique conditionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, initialNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    have innerReached : ∀ other ∈ body, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have terminal : (∃ nativeType, HasType (SourceCoreLocalCell.coreContext loopScope ++ administrative)
          (LocalLoop.iterate index.result childCode loopCode postCode escaped) nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge loopContext model index
          producer registry invocation faults administrative loopScope [] condition post body expected index.result
          (LocalLoop.iterate index.result childCode loopCode postCode escaped) budget ∧
        CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge loopContext model index
          producer registry invocation faults administrative loopScope [] condition post body expected index.result
          (LocalLoop.iterate index.result childCode loopCode postCode escaped) budget := by
      intro loopNative
      obtain ⟨_, loopNative⟩ := loopNative
      obtain ⟨⟨_, bodyNative⟩, ⟨_, postNative⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children loopNative
      have innerBounds := innerIH innerCovered innerReached (control := control.enterLoop) result loopSignatures
        bodyTyped ⟨_, bodyNative⟩
      have postBounds := CellAwareInvocationAcceptedForItems.post_correct (expected := expected) bridge bindings
        transport index producer registered registry invocation faults administrative budget expressions writes sourceEq
        unique artifact checked
        headReached.reached compilerFound form after afterCovered (fun item member => List.mem_append_right _ member)
        loopSignatures postTyped ⟨_, postNative⟩
      exact ⟨CellAwareInvocationAcceptedForItems.initial_preserves_of_valid bridge index producer registry invocation
          faults administrative fun runtime covers ledger => CellAwareInvocationForInitialTerminal.preserves bridge
            model producer transport (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
            (expressions fuel _ runtime covers ledger).1 (sourceEq ▸ conditionFound) nodeType
            (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.1 postBounds.1 ⟨_, _, _, bodyTyped⟩
            ⟨_, _, postTyped⟩,
        CellAwareInvocationAcceptedForItems.initial_reflects_of_valid bridge index producer registry invocation
          faults administrative fun runtime covers ledger => CellAwareInvocationForInitialTerminal.reflects bridge
            model producer transport (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
            (expressions fuel _ runtime covers ledger).2 (sourceEq ▸ conditionFound) nodeType
            (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.2.1 postBounds.2 ⟨_, _, _, bodyTyped⟩
            ⟨_, _, postTyped⟩⟩
    have initialBounds := CellAwareInvocationAcceptedForItems.initial_correct bridge bindings transport index producer
      registered registry invocation faults administrative budget expressions writes sourceEq unique artifact checked
      headReached.reached compilerFound form terminal initial initialCovered (fun item member => List.mem_append_left _ member)
      signatures initialTyped ⟨_, initialNative⟩
    refine ⟨?_, ?_, CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
    · intro size within mapping world actualContext environment canonical actual before store embedding
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready finalContext outcome after trace
      exact CellAwareInvocationForSequences.preserves bridge model producer sourceEq initialBounds.1 unique
        (sourceEq ▸ statementFound) form tailBounds.1 within environments heaps locals agrees actualTyped runtime covers
        sameLedger sourceTyped initial admitted authority physical owner sameLocation ready trace
    · intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed
      exact CellAwareInvocationForSequences.reflects bridge model producer sourceEq initialBounds.2
        (sourceEq ▸ statementFound) form tailBounds.2.1 within environments heaps locals agrees actualTyped runtime covers
        sameLedger sourceTyped initial admitted authority physical owner sameLocation ready completed
  | forBoundary => intro covered; cases covered
  | boundary => intro covered; cases covered

include bindings transport registered in
/-- The complete accepted body of an actual named or contextual invocation:
its compiler tree, footer and native result. Source executions of the original
statements are related in both directions at the actual reached heap. -/
theorem body_preserves (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
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
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  have flowNative : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative)
      body.flow nativeType whole.indexed.layouts.definitions := by
    obtain ⟨_, native⟩ := native
    rw [body.emitted] at native
    exact TypedLexicalWhile.Native.finished_flow native
  have bound := (correct bridge bindings transport index producer registered registry invocation faults
    administrative budget expressions writes artifact checked sourceEq unique body.tree covered (fun _ member => index.site_root member)
    result signatures sourceTyped flowNative).1
  intro size within
  rw [body.emitted]
  exact CellAwareInvocationBodyFinish.preserves bridge producer bound sourceEq sourceTyped depth projection
    index.fellThrough index.escaped within

include bindings transport registered in
/-- Native completion of the same complete accepted body reconstructs an
original Source execution, its body result and the reached heap. -/
theorem body_reflects (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
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
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  have flowNative : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative)
      body.flow nativeType whole.indexed.layouts.definitions := by
    obtain ⟨_, native⟩ := native
    rw [body.emitted] at native
    exact TypedLexicalWhile.Native.finished_flow native
  have bound := (correct bridge bindings transport index producer registered registry invocation faults
    administrative budget expressions writes artifact checked sourceEq unique body.tree covered (fun _ member => index.site_root member)
    result signatures sourceTyped flowNative).2.1
  intro size within
  rw [body.emitted]
  exact CellAwareInvocationBodyFinish.reflects bridge producer bound sourceEq sourceTyped depth projection
    index.fellThrough index.escaped within

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
