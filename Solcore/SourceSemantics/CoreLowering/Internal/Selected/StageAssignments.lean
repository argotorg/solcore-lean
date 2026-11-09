import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedForLoops

/-!
# Lifting to staged Source: assignments

Inversion and lifting of bare and projected assignments, resolution of projected targets, and projected `for` initializers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedAssignmentInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedAssignmentInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageForLiftBounds

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
  {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {size : Nat}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem statement_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    ∃ assignedSize updated, assignedSize < size ∧ finalContext = context ∧ outcome = .fallthrough environment ∧
      SourceExecutionSize.SourcePlaceAssignment program assignedSize context evidence source
        (Dynamic.AssignmentValueApplies operator) environment before assignment.target rhs updated after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
  refine ⟨_, ?_, _, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem statement_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ assignedSize, assignedSize < size ∧
      SourceExecutionSize.SourcePlaceAssignmentFaults program assignedSize context evidence source environment
        before assignment.target operator rhs reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

/-- Retain the genuine assignment derivation and independently measured suffix. -/
theorem child_and_tail {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceAssignmentFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target operator rhs reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceAssignment program assignedSize context invocation.evidence invocation.source
        (Dynamic.AssignmentValueApplies operator) environment before assignment.target rhs updated written ∧
      PlainStatements program mode tailSize invocation context environment written rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, head, tail⟩
  · obtain ⟨assignedSize, childStrict, failed⟩ := statement_fault unique found form failed
    exact .inl ⟨assignedSize, reason, Nat.lt_trans childStrict strict, equalContext, equalOutcome, failed⟩
  · obtain ⟨assignedSize, updated, childStrict, equalContext, equalOutcome, assigned⟩ :=
      statement_value unique found form head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · refine .inr ⟨assignedSize, SourceExecutionSize.stepSize [], updated, after,
        Nat.lt_trans childStrict strict, ?_, assigned, ?_⟩
      · simp only [SourceExecutionSize.stepSize, List.sum_nil]; omega
      · cases mode <;> exact .control .nil
  · obtain ⟨assignedSize, updated, childStrict, equalContext, equalOutcome, assigned⟩ :=
      statement_value unique found form head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨assignedSize, tailSize, updated, middle,
      Nat.lt_trans childStrict strict, tailStrict, assigned, tail⟩

theorem item_value {nextEnvironment : Dynamic.Environment}
    (trace : SourceExecutionSize.ForItemExecutes program size context evidence source environment
      before (.assignValue assignment operator rhs) finalContext nextEnvironment after) :
    ∃ assignedSize updated, assignedSize < size ∧ finalContext = context ∧ nextEnvironment = environment ∧
      SourceExecutionSize.SourcePlaceAssignment program assignedSize context evidence source
        (Dynamic.AssignmentValueApplies operator) environment before assignment.target rhs updated after := by
  cases trace with
  | assignValue assigned => exact ⟨_, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, assigned⟩

theorem item_fault
    (trace : SourceExecutionSize.ForItemFaults program size context evidence source environment
      before (.assignValue assignment operator rhs) reason after) :
    ∃ assignedSize, assignedSize < size ∧
      SourceExecutionSize.SourcePlaceAssignmentFaults program assignedSize context evidence source environment
        before assignment.target operator rhs reason after := by
  cases trace with
  | assignValue failed => exact ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), failed⟩

theorem item_and_tail {invocation : Staging.Recursive.Scope} {rest : List ForItemForm}
    (trace : PlainItems program size invocation context environment before
      (.assignValue assignment operator rhs :: rest) finalContext outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceAssignmentFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target operator rhs reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceAssignment program assignedSize context invocation.evidence invocation.source
        (Dynamic.AssignmentValueApplies operator) environment before assignment.target rhs updated written ∧
      PlainItems program tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | done trace =>
      cases trace with
      | cons head tail =>
          obtain ⟨assignedSize, updated, strict, rfl, rfl, assigned⟩ := item_value head
          exact .inr ⟨assignedSize, _, updated, _,
            Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
            SourceExecutionSize.child_lt_stepSize (by simp), assigned, .done tail⟩
  | fault trace =>
      cases trace with
      | head failed =>
          obtain ⟨assignedSize, strict, failed⟩ := item_fault failed
          exact .inl ⟨assignedSize, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)), rfl, rfl, failed⟩
      | tail head failed =>
          obtain ⟨assignedSize, updated, strict, rfl, rfl, assigned⟩ := item_value head
          exact .inr ⟨assignedSize, _, updated, _,
            Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
            SourceExecutionSize.child_lt_stepSize (by simp), assigned, .fault failed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedAssignmentInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds
open Staging.Recursive (BareTarget)

private theorem target_functional {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {place : PlaceResolution} {left right : Dynamic.ResolvedPlace}
    (first : BareTarget environment heap place left) (second : BareTarget environment heap place right) : left = right := by
  cases first with
  | intro _ leftLookup leftRead leftValue =>
    cases second with
    | intro _ rightLookup rightRead rightValue =>
      cases leftLookup.functional rightLookup
      cases leftRead.functional rightRead
      cases leftValue.functional rightValue
      rfl

private theorem resolve_same {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target actual : Dynamic.ResolvedPlace} {size : Nat}
    (snapshot : BareTarget environment before place target)
    (resolved : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place actual after) :
    after = before ∧ actual = target := by
  have bare : place.projections = [] := by cases snapshot; assumption
  obtain ⟨same, other⟩ := BareTarget.of_resolves bare resolved.sound
  exact ⟨same.symm, target_functional other snapshot⟩

private theorem target_fault_excluded {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target : Dynamic.ResolvedPlace} {reason : Dynamic.SemanticFault}
    (snapshot : BareTarget environment before place target)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after) : False := by
  cases snapshot with
  | intro bare present cell initial =>
    cases fault with
    | unbound missing => exact missing.excludes_lookup present
    | dangling lookup missing =>
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionExpression _ _ failed => rw [bare] at failed; cases failed
    | danglingAfterProjections lookup _ evaluated missing =>
      rw [bare] at evaluated
      cases evaluated
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionRead _ _ evaluated _ _ failed =>
      rw [bare] at evaluated
      cases evaluated
      cases failed
    | uninitialized _ _ evaluated _ _ _ nonempty =>
      rw [bare] at evaluated
      cases evaluated
      exact nonempty rfl

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {target : Dynamic.ResolvedPlace} {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem statement_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    ∃ child value middle updated, child < size ∧ finalContext = context ∧ outcome = .fallthrough environment ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before rhs value middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
  rename_i assigned
  cases assigned with
  | intro resolved evaluated written =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    refine ⟨_, ?_, _, _, evaluated, _, written⟩
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
    omega

private theorem statement_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    (∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before rhs reason after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧
      reason = .invalidAssignmentOperands operator ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before rhs right after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ child right currentCell initial currentSelected code, child < size ∧
      reason = .panic code ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before rhs right after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsPanic operator target.selected right code) := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  obtain ⟨rfl, rfl, rfl⟩ := ‹_ ∧ _ ∧ _›
  rename_i failed
  cases failed with
  | target failed => exact (target_fault_excluded snapshot failed.sound).elim
  | rhs resolved failed =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    refine .inl ⟨_, ?_, failed⟩
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
    omega
  | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    refine .inr (.inl ⟨_, ?_, rfl, _, evaluated, _, currentRead, rootType, _, initialValue, ⟨_, pathRead⟩, invalid⟩)
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
    omega
  | panic resolved evaluated currentRead rootType initialValue pathRead panics =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    refine .inr (.inr ⟨_, ?_, _, _, _, _, _, rfl, evaluated, currentRead, rootType, initialValue, pathRead, panics⟩)
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
    omega
  | structuralUpdate resolved _ _ _ _ failed =>
    obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
    cases snapshot
    cases failed

/-- The exact pre-expression target determines the ordinary write after the
right-hand expression. Operand rejection keeps the successful RHS prefix and
its exact current-root traversal, without a write or suffix. -/
theorem child_and_tail {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.fault reason) after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧ finalContext = context ∧
      outcome = .fault (.invalidAssignmentOperands operator) ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ child right currentCell initial currentSelected code, child < size ∧ finalContext = context ∧
      outcome = .fault (.panic code) ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsPanic operator target.selected right code) ∨
    (∃ child tailSize value middle updated written, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      PlainStatements program mode tailSize invocation context environment written rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, head, tail⟩
  · rcases statement_fault unique found form snapshot failed with
      ⟨child, childStrict, failed⟩ |
      ⟨child, right, currentCell, initial, currentSelected, childStrict, reasonEq, evaluated,
        currentRead, rootType, initialValue, pathRead, invalid⟩ |
      ⟨child, right, currentCell, initial, currentSelected, code, childStrict, reasonEq, evaluated,
        currentRead, rootType, initialValue, pathRead, panics⟩
    · exact .inl ⟨child, reason, Nat.lt_trans childStrict strict, equalContext, equalOutcome, .fault failed⟩
    · subst reason
      exact .inr (.inl ⟨child, right, currentCell, initial, currentSelected, Nat.lt_trans childStrict strict,
        equalContext, equalOutcome, .value evaluated, currentRead, rootType, initialValue, pathRead, invalid⟩)
    · subst reason
      exact .inr (.inr (.inl ⟨child, right, currentCell, initial, currentSelected, code, Nat.lt_trans childStrict strict,
        equalContext, equalOutcome, .value evaluated, currentRead, rootType, initialValue, pathRead, panics⟩))
  · obtain ⟨child, value, middle, updated, childStrict, equalContext, equalOutcome, evaluated, written⟩ :=
      statement_value unique found form snapshot head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · refine .inr (.inr (.inr ⟨child, SourceExecutionSize.stepSize [], value, middle, updated, after,
        Nat.lt_trans childStrict strict, ?_, .value evaluated, written, ?_⟩))
      · simp only [SourceExecutionSize.stepSize, List.sum_nil]; omega
      · cases mode <;> exact .control .nil
  · obtain ⟨child, value, expressionHeap, updated, childStrict, equalContext, equalOutcome, evaluated, written⟩ :=
      statement_value unique found form snapshot head
    subst middleContext
    cases equalOutcome
    exact .inr (.inr (.inr ⟨child, tailSize, value, expressionHeap, updated, middle,
      Nat.lt_trans childStrict strict, tailStrict, .value evaluated, written, tail⟩))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedResolutionLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedResolutionLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open SourceCoreCompatibleDataPlaces
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {values : SourceCoreCompatibleValues.Context} {receiving : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry receiving)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
  {place : PlaceResolution} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {rhsType : Core.Ty} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty} {administrative : Core.Context}

local notation "model" => CompatibleAmbientHeap.payloadModel values.checked receiving functions

include extension transport faithful observations in
/-- Ordinary key effects are lifted before the getter and before any RHS. -/
theorem lifts (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (keyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model stages invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before after : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
    {index : Nat} {target : Dynamic.ResolvedPlace} {size : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : SourceExecutionSize.SourcePlaceResolves program size context invocation.evidence invocation.source
      environment before place target after) (within : size ≤ budget) :
    (∃ origin call reason reached,
      Staging.Recursive.ProjectedTarget.RootReady environment before place ∧
      Staging.Recursive.Expressions program stages invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.fault (.stage origin call reason)) reached) ∨
    (∃ sources,
      Staging.Recursive.Expressions program stages invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) after ∧
      Staging.Recursive.ProjectedTarget.Snapshot environment before after place sources target ∧
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧
      ∃ resolution : CompatiblePlaceResolution.Execution values.checked receiving functions prepared
        (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before after,
        ∃ reached : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, after, resolution.store, canonical⟩,
          callerProtocol.Relates initial reached ∧ Admission bridge context reached) := by
  obtain ⟨keySize, sources, keyBound, ordinaryKeys, snapshot⟩ := SelectedCompilationStageProjectedTargetInversion.resolved trace
  have rowTyped := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed layout.children unique keyTyped
  obtain ⟨outcome, reached, stagedKeys, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
    layout.children unique rowTyped children preservation environments heaps locals agrees actualTyped initial admitted
    (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
    (Nat.le_trans (Nat.le_of_lt keyBound) within)
  have keyTrace : Staging.Recursive.Expressions program stages invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) outcome reached := by
    simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using stagedKeys
  cases adapted with
  | rejected origin call reason reached =>
      refine .inl ⟨origin, call, reason, reached, ?_, keyTrace⟩
      cases snapshot with
      | intro lookup read _ _ _ _ => exact .intro lookup read
  | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expressions.of_trace keyTrace
      obtain ⟨resolution, _sameSources, keyValues, _keyHeap, _lookup, reached, related, admitted⟩ :=
        CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_resolution bridge stagedSize layout ordinary
          extension transport faithful observations environments heaps locals agrees actualTyped initial admitted unique
          keyTyped (fun n _ => preservation n) slot writable measured (Nat.le_refl _) snapshot
      exact .inr ⟨sources, keyTrace, snapshot, keyValues, resolution, reached, related, admitted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedResolutionLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedAssignmentLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions



include bridge functions faithful observations condition transport extension in
/-- Ordered keys, getter, RHS and real write are lifted at their actual states. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetType, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  rcases head with ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, shape, slot, writable, rhsFound, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary =>
    let head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
        certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs :=
      ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, .projected layout ordinary,
        slot, writable, rhsFound, generated, rightView, rightType, profile⟩
    have keyTyped := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed layout.children unique originalKeyTyped
    have liftResolved {resolvedTarget : Dynamic.ResolvedPlace} {resolvedHeap : Dynamic.Heap} {resolvedGrade : Nat}
        (resolved : SourceExecutionSize.SourcePlaceResolves program resolvedGrade context invocation.evidence invocation.source
          environment before assignment.target resolvedTarget resolvedHeap) (bounded : resolvedGrade ≤ budget) :=
      SelectedCompilationStageProjectedResolutionLifting.lifts
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (stages := stages) (faults := faults)
        bridge functions extension transport
        faithful observations budget layout ordinary unique originalKeyTyped children preservation
        environments heaps locals agrees actualTyped initial admitted head.slot head.writable resolved bounded
    rcases SelectedCompilationStageProjectedAssignmentInversion.child_and_tail unique found form trace with
      ⟨assignedSize, reason, strict, rfl, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, .assignProjectedRootFault (lookupStatement?_sound found) form projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .assignProjectedGetterFault (lookupStatement?_sound found) form projected keys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedWriteFault (lookupStatement?_sound found) form projected keys snapshot lifted (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | panic resolved evaluated currentRead rootType initialValue pathRead panics =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedWriteFault (lookupStatement?_sound found) form projected keys snapshot lifted (.panic currentRead rootType initialValue pathRead panics), .completed (.fault (.panic _))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedWriteFault (lookupStatement?_sound found) form projected keys snapshot lifted (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
            obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            obtain ⟨rhsStageSize, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
                _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_value
                (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (stages := stages) (faults := faults)
                bridge functions extension transport
                faithful observations head projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                (keyStageSize + rhsStageSize + 1) (fun n _ => preservation n)
                measuredKeys (by omega) snapshot measuredRhs (by omega) write
            obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
              (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds) middleHeaps
              (locals.mono metadata) (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped reference
              ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned nextAdmitted tail
            exact ⟨nextContext, result, finalHeap,
              .assignProjected (lookupStatement?_sound found) form projected keys snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions



include bridge functions condition transport extension in
/-- Value assignment lifts the RHS at the original target snapshot. The
existing real write producer supplies the next physical state for the suffix. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative)
    functions extension head bare environments heaps locals agrees
  rcases SelectedCompilationStageAssignmentInversion.child_and_tail unique found form snapshot trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, strict, rfl, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, code, strict, rfl, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, panics⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, strict, tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareOperands (lookupStatement?_sound found) form snapshot lifted
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBarePanic (lookupStatement?_sound found) form snapshot lifted
        currentRead rootType rootInitial pathRead panics, .completed (.fault (.panic _))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_value
          (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          (preservation stagedSize) snapshot measured write
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds) middleHeaps
        (locals.mono metadata) (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped reference
        ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        middleState conditioned nextAdmitted tail
      exact ⟨nextContext, result, finalHeap,
        .assignBare (lookupStatement?_sound found) form snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialProjectedInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
open Frontend SourceInference
open SelectedCompilationStageForInitialBounds

/-- Preserve the actual assignment grade before the remaining initialization. -/
theorem assignProjected {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {items post : List ForItemForm} {test : ExpressionId} {body : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (trace : PlainInitial program invocation context environment before
      (.assignValue assignment operator rhs :: items) test post body size outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceAssignmentFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target operator rhs reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceAssignment program assignedSize context invocation.evidence invocation.source
        (Dynamic.AssignmentValueApplies operator) environment before assignment.target rhs updated written ∧
      PlainInitial program invocation context environment written items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · obtain ⟨assignedSize, assignedStrict, failed⟩ := SelectedCompilationStageProjectedAssignmentInversion.item_fault failed
    exact .inl ⟨assignedSize, reason, Nat.lt_trans assignedStrict strict, same, failed⟩
  · obtain ⟨assignedSize, updated, assignedStrict, rfl, rfl, assigned⟩ :=
      SelectedCompilationStageProjectedAssignmentInversion.item_value executed
    rw [restored tail] at same
    subst outcome
    exact .inr ⟨assignedSize, _, updated, _, Nat.lt_trans assignedStrict childStrict, tailStrict, assigned, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialProjectedLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions



include bridge functions faithful observations condition transport extension in
/-- Ordered keys, getter, RHS and real write are lifted at their actual states. -/
theorem assignProjected {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignValue assignment operator rhs :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetType, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  rcases head with ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, shape, slot, writable, rhsFound, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary =>
    let head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
        certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs :=
      ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, .projected layout ordinary,
        slot, writable, rhsFound, generated, rightView, rightType, profile⟩
    have keyTyped := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed layout.children unique originalKeyTyped
    have liftResolved {resolvedTarget : Dynamic.ResolvedPlace} {resolvedHeap : Dynamic.Heap} {resolvedGrade : Nat}
        (resolved : SourceExecutionSize.SourcePlaceResolves program resolvedGrade context invocation.evidence invocation.source
          environment before assignment.target resolvedTarget resolvedHeap) (bounded : resolvedGrade ≤ budget) :=
      SelectedCompilationStageProjectedResolutionLifting.lifts
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (stages := stages) (faults := faults)
        bridge functions extension transport
        faithful observations budget layout ordinary unique originalKeyTyped children preservation
        environments heaps locals agrees actualTyped initial admitted head.slot head.writable resolved bounded
    rcases SelectedCompilationStageForInitialInversion.assignProjected trace with
      ⟨assignedSize, reason, strict, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_root_fault projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_getter_fault projected measuredKeys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected measuredKeys snapshot measuredRhs (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | panic resolved evaluated currentRead rootType initialValue pathRead panics =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected measuredKeys snapshot measuredRhs (.panic currentRead rootType initialValue pathRead panics), .completed (.fault (.panic _))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected measuredKeys snapshot measuredRhs (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
            obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            obtain ⟨rhsStageSize, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
                _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_value
                (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (stages := stages) (faults := faults)
                bridge functions extension transport
                faithful observations head projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                (keyStageSize + rhsStageSize + 1) (fun n _ => preservation n)
                measuredKeys (by omega) snapshot measuredRhs (by omega) write
            obtain ⟨nextSize, result, finalHeap, restTrace, restAdapted⟩ := remaining
              (Nat.le_trans (Nat.le_of_lt tailStrict) within)
              ⟨_, _, _, environments.extend maps worlds, middleHeaps,
                locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
                ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
                (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
                middleState, conditioned, nextAdmitted⟩ tail
            exact ⟨_, result, finalHeap,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_assignment
                projected measuredKeys snapshot measuredRhs write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
end
