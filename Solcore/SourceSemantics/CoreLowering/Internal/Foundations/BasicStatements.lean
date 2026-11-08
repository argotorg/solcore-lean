import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.Frontend.SourceCore.Lowering
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.Core.Internal.Renaming
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GeneralExpressions

/-!
# Basic statements

Basic statements with their certificates and meaning, and general statements.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
/-! The lexical tree uses one fixed physical frame and stable native token.
Every allocation consumes its actual reached-state witness and a real live
read. Readiness is supplied by a logical acquisition family, independently of
source/native expression or body execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.CellAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory
universe u v

variable {Records : Type v} {protocol : Protocol.{u, v} Records}
  {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}
  {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
  {model : GenericHeap.CellModel nativeDefinitions}

def ReadyAt (producer : Producer (catalog := catalog) protocol layouts frame model)
    (location : Location) (native : NativeFrame) : Prop :=
  ∀ {index : Index} (reached : protocol.State index),
    index.store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native) →
    producer.Ready reached location native

/-- The certified administrative effect supplies the reached read, including
after expression children and completed source allocations. -/
theorem ReadyAt.after_administrative {producer : Producer (catalog := catalog) protocol layouts frame model}
    {location : Location} {native : NativeFrame}
    (ready : ReadyAt producer location native)
    {initial reached : Index} (state : protocol.State reached)
    (read : initial.store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : location ∉ initial.mapping)
    (preserved : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    producer.Ready state location native := by
  exact ready state ((preserved location unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)

theorem administrative_readyAt (protocol : Protocol.{u, v} Records)
    (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
    (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout)
    (model : GenericHeap.CellModel nativeDefinitions)
    (location : Location) (native : NativeFrame) :
    ReadyAt (of_administrative (catalog := catalog) protocol transport bindings layouts frame model) location native :=
  fun _state _read => True.intro

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.CellAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BasicStatementCertificates
/-! Static certificates for the executable basic statement lowerer.
The theorem consumes the actual successful compiler result, including all
metadata and scope checks. It assumes no source or Core execution. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell

private theorem bind_ok {α β : Type} {computation : Except SourceCoreBasic.Error α}
    {next : α → Except SourceCoreBasic.Error β} {result : β}
    (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem projectType_types
    {site : SourceCoreElaboration.ErrorSite} {sourceType : Ty} {type : Core.Ty}
    (projected : SourceCoreBasic.projectType site sourceType = .ok type) :
    TypeRepresents sourceType type := by
  unfold SourceCoreBasic.projectType at projected
  cases result : SourceCoreElaboration.lowerType site sourceType with
  | error error => simp [result, Except.mapError] at projected
  | ok lowered =>
      simp only [result, Except.mapError, Except.ok.injEq] at projected
      subst lowered
      exact BasicExpressions.typeRepresents_of_lowerType result

structure Metadata (source : TypedSource) (id : StatementId)
    (node : StatementNode) (type : Core.Ty) : Prop where
  contains : ContainsStatement source id node
  owned : id.occurrence.owner = source.owner
  types : TypeRepresents node.type type

theorem readStatement_certificate
    {source : TypedSource} {id : StatementId} {node : StatementNode} {type : Core.Ty}
    (read : SourceCoreBasic.readStatement source id = .ok (node, type)) :
    source.lookupStatement? id = some node ∧ Metadata source id node type := by
  by_cases owned : id.occurrence.owner = source.owner
  · cases found : source.lookupStatement? id with
    | none => simp [SourceCoreBasic.readStatement, owned, found, bind, Except.bind] at read
    | some selected =>
        cases projected : SourceCoreBasic.projectType (.occurrence id.occurrence) selected.type with
        | error error =>
            simp [SourceCoreBasic.readStatement, owned, found, projected,
              bind, Except.bind, pure, Pure.pure, Except.pure] at read
        | ok projectedType =>
            simp [SourceCoreBasic.readStatement, owned, found, projected,
              bind, Except.bind, pure, Pure.pure, Except.pure] at read
            rcases read with ⟨rfl, rfl⟩
            exact ⟨rfl, lookupStatement?_sound found, owned, projectType_types projected⟩
  · simp [SourceCoreBasic.readStatement, owned, bind, Except.bind] at read

/-- These are executable binder restrictions, not the stronger declarative
`BinderExtends` judgment about the complete source static context. -/
structure BinderCertificate (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (binder : TypedBinder) (type : Core.Ty) : Prop where
  owned : binder.id.owner = source.owner
  monomorphic : binder.scheme.quantified = []
  requirements : binder.schemeRequirements = []
  runtime : binder.comptime = false
  fresh : scope.any (fun entry => decide (entry.1 = binder.id)) = false
  types : TypeRepresents binder.scheme.body type

theorem lowerBinder_certificate
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {type : Core.Ty}
    (accepted : SourceCoreBasic.lowerBinder source scope binder = .ok type) :
    BinderCertificate source scope binder type := by
  by_cases owned : binder.id.owner = source.owner
  · by_cases monomorphic : binder.scheme.quantified = []
    · by_cases requirements : binder.schemeRequirements = []
      · cases runtime : binder.comptime with
        | true =>
            simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
              runtime, bind, Except.bind] at accepted
        | false =>
            cases fresh : scope.any (fun entry => decide (entry.1 = binder.id)) with
            | true =>
                simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
                  runtime, fresh, bind, Except.bind] at accepted
            | false =>
                simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
                  runtime, fresh] at accepted
                exact ⟨owned, monomorphic, requirements, runtime, fresh, projectType_types accepted⟩
      · simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
          bind, Except.bind] at accepted
    · simp [SourceCoreBasic.lowerBinder, owned, monomorphic,
        bind, Except.bind] at accepted
  · simp [SourceCoreBasic.lowerBinder, owned, bind, Except.bind] at accepted

structure AssignmentCertificate (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (index : Nat) (type : Core.Ty) : Prop where
  equal : operator = .equal
  owned : assignment.target.root.owner = source.owner
  requirements : assignment.requirements = []
  bare : assignment.target.projections = []
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, type)
  types : TypeRepresents assignment.target.type type

theorem lowerAssignment_certificate
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {index : Nat} {type : Core.Ty}
    (accepted : SourceCoreBasic.lowerAssignment source scope assignment operator = .ok (index, type)) :
    AssignmentCertificate source scope assignment operator index type := by
  by_cases equal : operator = .equal
  · by_cases owned : assignment.target.root.owner = source.owner
    · by_cases requirements : assignment.requirements = []
      · by_cases bare : assignment.target.projections = []
        · cases slot : SourceCoreLocalCell.lookup? scope assignment.target.root with
          | none =>
              simp [SourceCoreBasic.lowerAssignment, equal, owned, requirements, bare, slot,
                bind, Except.bind] at accepted
          | some found =>
              rcases found with ⟨foundIndex, foundType⟩
              simp only [SourceCoreBasic.lowerAssignment, equal, owned, requirements, bare, slot,
                ne_eq, not_true_eq_false, ↓reduceIte, List.isEmpty_nil,
                bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
              obtain ⟨projected, projection, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have same := ensureType_ok checked
              cases accepted
              exact ⟨equal, owned, requirements, bare, slot, same ▸ projectType_types projection⟩
        · simp [SourceCoreBasic.lowerAssignment, equal, owned, requirements, bare,
            bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      · simp [SourceCoreBasic.lowerAssignment, equal, owned, requirements,
          bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    · simp [SourceCoreBasic.lowerAssignment, equal, owned, bind, Except.bind] at accepted
  · simp [SourceCoreBasic.lowerAssignment, equal, bind, Except.bind] at accepted

private theorem expression_typing
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) lowered.expression
      (Core.LanguageResult.resultType lowered.type) ∧ Core.CellPayload lowered.type := by
  obtain ⟨_, _, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
  exact ⟨tree.hasType, tree.cellPayload⟩

/-- All accepted basic statement lists have the declared Core result type.
Explicit returns intentionally need no certificate for their unreachable tail.
The scalar/product result invariant is extracted at the same time. -/
theorem lowerStatements_typing
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {resultType : Core.Ty} {reason : Core.Word}
    {expression : Core.Expr}
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason =
      .ok expression) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) expression
      (Core.LanguageResult.resultType resultType) ∧ Core.CellPayload resultType := by
  induction fuel generalizing scope statements expression with
  | zero =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨Core.LanguageResult.success_hasType .unit, .unit⟩
          · cases accepted
      | cons => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨Core.LanguageResult.success_hasType .unit, .unit⟩
          · cases accepted
      | cons id rest =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have binderCertificate := lowerBinder_certificate binding
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
                  exact ⟨Core.LocalSequence.letUninitialized_hasType
                    (binderCertificate.types.wellFormed []) bodyTyped, resultPayload⟩
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
                  have valueTyped := (expression_typing compiledValue).1
                  rw [← same] at valueTyped
                  exact ⟨Core.LocalSequence.letInitialized_hasType resultPayload.wellFormed
                    valueTyped bodyTyped, resultPayload⟩
          | assignValue assignment operator value =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have same := ensureType_ok checked
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
              have targetCertificate := lowerAssignment_certificate target
              have valueTyped := (expression_typing compiledValue).1
              rw [← same] at valueTyped
              exact ⟨Core.LocalSequence.assign_hasType resultPayload.wellFormed
                (.var (SourceCoreLocalCell.lookup?_context targetCertificate.slot))
                valueTyped bodyTyped, resultPayload⟩
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultSame := ensureType_ok resultChecked
                  have unitSame := ensureType_ok unitChecked
                  have resultUnit : resultType = .unit := resultSame.trans unitSame.symm
                  cases accepted
                  rw [resultUnit]
                  exact ⟨Core.LanguageResult.success_hasType .unit, .unit⟩
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  cases accepted
                  rw [same]
                  exact expression_typing compiledValue
          | expression value semicolon =>
              cases semicolon with
              | true =>
                  simp only [form, ↓reduceIte] at accepted
                  obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
                  exact ⟨Core.LocalSequence.discard_hasType resultPayload.wellFormed
                    (expression_typing compiledValue).1 bodyTyped, resultPayload⟩
              | false =>
                  simp only [form, Bool.false_eq_true, ↓reduceIte] at accepted
                  split at accepted
                  · obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    have same := ensureType_ok checked
                    cases accepted
                    rw [same]
                    exact expression_typing compiledValue
                  · cases accepted
          | assignBitNot | ifThen | block | matchWith | forLoop | whileLoop | breakStmt | continueStmt =>
              simp [form] at accepted

theorem lowerStatements_hasType
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {resultType : Core.Ty} {reason : Core.Word}
    {expression : Core.Expr}
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason =
      .ok expression) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) expression
      (Core.LanguageResult.resultType resultType) :=
  (lowerStatements_typing accepted).1

theorem lowerStatements_infer
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {resultType : Core.Ty} {reason : Core.Word}
    {expression : Core.Expr}
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason =
      .ok expression) :
    Core.infer? (SourceCoreLocalCell.coreContext scope) expression =
      some (Core.LanguageResult.resultType resultType) :=
  Core.infer_complete (lowerStatements_hasType accepted)

end Solcore.SourceSemantics.CoreLowering.BasicStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BasicStatements
/-! Composition laws for the actual ordinary-local statement compiler.

Each law combines independent source derivations with child Core derivations
and an equation of `SourceCoreBasic.lowerStatements`. Temporary result binders
are explicit in the Core premises. No unrestricted heap weakening, whole-body
compiler correctness, staging correctness or termination theorem is assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem

private theorem prepend
    {program : Program} {context middleContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment nextEnvironment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id
      middleContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program middleContext evidence source
      nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      (id :: rest) finalContext outcome after := by
  cases rest with
  | nil =>
      cases tail with
      | control execute =>
          cases execute
          exact .control (.singleton contains notTail head)
      | fault fault => cases fault
  | cons next rest =>
      cases tail with
      | control execute => exact .control (.cons head execute)
      | fault fault => exact .fault (.tail head fault)

private theorem fault_prefix
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {reason : Dynamic.SemanticFault} (rest : List StatementId)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      (id :: rest) context (.fault reason) after := by
  cases rest with
  | nil => exact .fault (.singleton fault)
  | cons _ _ => exact .fault (.head fault)

private theorem returned_prefix
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {value : Dynamic.Value} (rest : List StatementId)
    (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (returned : Dynamic.StatementExecutes program context evidence source environment before id
      context (.returned value) after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      (id :: rest) context (.returned value) after := by
  cases rest with
  | nil => exact .control (.singleton contains notTail returned)
  | cons _ _ => exact .control (.terminal returned (.returned value))

section Prefix

variable {program : Program} {context middleContext finalContext : Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {environment : Dynamic.Environment}
  {coreEnvironment : Core.Environment} {before middle after : Dynamic.Heap}
  {store middleStore finalStore : Core.Store} {world : Core.StoreTyping}
  {fuel : Nat} {id : StatementId} {rest : List StatementId} {node : StatementNode}
  {resultType : Core.Ty} {reason : Core.Word} {body : Core.Expr}
  {outcome : Dynamic.ControlOutcome} {result : Core.Value}

/-- Allocation chooses the same source/Core location before the continuation. -/
theorem letUninitialized_prefix
    {binder : TypedBinder} {payloadType : Core.Ty} {location : Dynamic.Location}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder none)
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok payloadType)
    (monomorphic : binder.scheme.quantified = [])
    (extension : BinderExtends source.owner context binder middleContext)
    (types : LocalCell.TypeRepresents binder.scheme.body payloadType)
    (related : LocalCell.HeapRepresents before.cells store world)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location middle)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source
      ((binder.id, payloadType) :: scope) rest resultType reason = .ok body)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program middleContext evidence source
      ((binder.id, location) :: environment) middle rest finalContext outcome after)
    (tailCore : Core.Evaluates
      (.cellRef (Core.OptionalCell.cellType payloadType) location.index :: coreEnvironment)
      (store ++ [.inLeft payloadType .unit]) body result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.letUninitialized payloadType body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store (Core.LocalSequence.letUninitialized payloadType body)
        result finalStore := by
  refine ⟨SourceCoreBasic.lowerStatements_letUninitialized metadata form binding tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.letUninitialized contains form monomorphic extension allocated) tailSource, ?_⟩
  have locationEq := (related.allocate_uninitialized types allocated).1
  exact Core.LocalSequence.letUninitialized_evaluates payloadType (locationEq ▸ tailCore)

/-- Initializer effects precede allocation. The Core continuation is evaluated
with the successful payload inserted after its new lexical cell reference. -/
theorem letInitialized_prefix
    {binder : TypedBinder} {initializer : ExpressionId} {expression : Core.Expr}
    {location : Dynamic.Location} {allocatedHeap : Dynamic.Heap}
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder (some initializer))
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok (SourceStagedValue.coreType value))
    (monomorphic : binder.scheme.quantified = [])
    (extension : BinderExtends source.owner context binder middleContext)
    (binderType : binder.scheme.body = SourceStagedValue.sourceType value)
    (initializerLowered : SourceCoreBasic.lowerExpression fuel source scope initializer reason =
      .ok ⟨SourceStagedValue.coreType value, expression⟩)
    (initializerSource : Dynamic.ExpressionEvaluates program context evidence source environment
      before initializer (StagedValue.toSource value) middle)
    (initializerCore : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) middleStore)
    (related : LocalCell.HeapRepresents middle.cells middleStore world)
    (allocated : Dynamic.Heap.Allocates middle binder.scheme.body
      (some (StagedValue.toSource value)) location allocatedHeap)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source
      ((binder.id, SourceStagedValue.coreType value) :: scope) rest resultType reason = .ok body)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program middleContext evidence source
      ((binder.id, location) :: environment) allocatedHeap rest finalContext outcome after)
    (tailCore : Core.Evaluates
      (.cellRef (Core.OptionalCell.cellType (SourceStagedValue.coreType value)) location.index ::
        SourceStagedValue.toCore value :: coreEnvironment)
      (middleStore ++ [.inRight .unit (SourceStagedValue.toCore value)])
      (body.weakenAt 1) result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.letInitialized resultType (SourceStagedValue.coreType value) expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.letInitialized resultType (SourceStagedValue.coreType value) expression body)
        result finalStore := by
  refine ⟨SourceCoreBasic.lowerStatements_letInitialized metadata form binding initializerLowered tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.letInitialized contains form initializerSource monomorphic extension allocated) tailSource, ?_⟩
  have locationEq := (related.allocate_initialized value (binderType ▸ allocated)).1
  exact Core.LocalSequence.letInitialized_success resultType (SourceStagedValue.coreType value)
    initializerCore (locationEq ▸ tailCore)

theorem discard_prefix
    {expressionId : ExpressionId} {valueType : Core.Ty} {expression : Core.Expr}
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .expression expressionId true)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨valueType, expression⟩)
    (expressionSource : Dynamic.ExpressionEvaluates program context evidence source environment
      before expressionId (StagedValue.toSource value) middle)
    (expressionCore : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) middleStore)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program context evidence source
      environment middle rest finalContext outcome after)
    (tailCore : Core.Evaluates (SourceStagedValue.toCore value :: coreEnvironment) middleStore
      (body.weakenAt 0) result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.discard resultType expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store (Core.LocalSequence.discard resultType expression body)
        result finalStore := by
  exact ⟨SourceCoreBasic.lowerStatements_discard metadata form lowered tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.expression contains form expressionSource) tailSource,
    Core.LocalSequence.discard_success resultType expressionCore tailCore⟩

/-- The reference is captured before RHS evaluation. The store supplied by the
RHS is the one read and written; temporary binders are exposed in the premises. -/
theorem assign_prefix
    {assignment : AssignmentResolution} {rhs : ExpressionId} {expression : Core.Expr}
    {index : Nat} {payloadType : Core.Ty} {location : Core.Location}
    {rhsStore : Core.Store} {updatedRoot : Dynamic.Value} {value oldValue : Core.Value}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .assignValue assignment .equal rhs)
    (target : SourceCoreBasic.lowerAssignment source scope assignment .equal = .ok (index, payloadType))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope rhs reason = .ok ⟨payloadType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (assignmentSource : Dynamic.SourcePlaceAssignment program context evidence source
      (Dynamic.AssignmentValueApplies .equal) environment before assignment.target rhs updatedRoot middle)
    (lookup : coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) location))
    (rhsCore : Core.Evaluates (.cellRef (Core.OptionalCell.cellType payloadType) location :: coreEnvironment)
      store (expression.weakenAt 0) (.inRight .word value) rhsStore)
    (readable : rhsStore.read? location = some oldValue)
    (written : rhsStore.write? location (.inRight .unit value) = some middleStore)
    (tailSource : Dynamic.FunctionStatementsExecuteOutcome program context evidence source
      environment middle rest finalContext outcome after)
    (tailCore : Core.Evaluates
      (.unit :: value :: .cellRef (Core.OptionalCell.cellType payloadType) location :: coreEnvironment)
      middleStore (((body.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.assign resultType (.var index) expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) finalContext outcome after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.assign resultType (.var index) expression body) result finalStore := by
  exact ⟨SourceCoreBasic.lowerStatements_assign metadata form target lowered tailLowered,
    prepend contains (by intro expression; rw [form]; intro impossible; cases impossible)
      (.assignValue contains form assignmentSource) tailSource,
    Core.LocalSequence.assign_success resultType (.var lookup) rhsCore readable written tailCore⟩

end Prefix

section Terminal

variable {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : SourceCoreBasic.Scope} {environment : Dynamic.Environment}
  {coreEnvironment : Core.Environment} {before after : Dynamic.Heap} {store finalStore : Core.Store}
  {fuel : Nat} {id : StatementId} {rest : List StatementId} {node : StatementNode}
  {resultType : Core.Ty} {reason : Core.Word} {expression : Core.Expr} {expressionId : ExpressionId}

/-- A return never requires lowering or evaluating any trailing statement. -/
theorem return_prefix
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .returnStmt (some expressionId))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment
      before expressionId (StagedValue.toSource value) after)
    (coreEvaluation : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.returned (StagedValue.toSource value)) after ∧
      Core.Evaluates coreEnvironment store expression
        (.inRight .word (SourceStagedValue.toCore value)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_return metadata form lowered,
    returned_prefix rest contains
      (by intro expression; rw [form]; intro impossible; cases impossible)
      (.returnValue contains form sourceEvaluation), coreEvaluation⟩

theorem returnUnit_prefix
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .returnStmt none) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) .unit reason =
        .ok (Core.LanguageResult.success .unit) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.returned .unit) before ∧
      Core.Evaluates coreEnvironment store (Core.LanguageResult.success .unit)
        (.inRight .word .unit) store :=
  ⟨SourceCoreBasic.lowerStatements_returnUnit metadata form,
    returned_prefix rest contains
      (by intro expression; rw [form]; intro impossible; cases impossible)
      (.returnUnit contains form), .inRight .unit⟩

theorem tailExpression
    (value : SourceStagedValue.Value)
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .expression expressionId false)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment
      before expressionId (StagedValue.toSource value) after)
    (coreEvaluation : Core.Evaluates coreEnvironment store expression
      (.inRight .word (SourceStagedValue.toCore value)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope [id] resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        [id] context (.returned (StagedValue.toSource value)) after ∧
      Core.Evaluates coreEnvironment store expression
        (.inRight .word (SourceStagedValue.toCore value)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_tail metadata form lowered,
    .control (.tailExpression contains form sourceEvaluation), coreEvaluation⟩

theorem return_fault
    {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .returnStmt (some expressionId))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_return metadata form lowered,
    fault_prefix rest (.returnValue contains form sourceFault), coreFailure⟩

theorem tailExpression_fault
    {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, resultType))
    (form : node.form = .expression expressionId false)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨resultType, expression⟩)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope [id] resultType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        [id] context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store expression (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_tail metadata form lowered,
    .fault (.tailExpression contains form sourceFault), coreFailure⟩

theorem letInitialized_fault
    {binder : TypedBinder} {payloadType : Core.Ty} {body : Core.Expr}
    {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder (some expressionId))
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok payloadType)
    (monomorphic : binder.scheme.quantified = [])
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨payloadType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source ((binder.id, payloadType) :: scope)
      rest resultType reason = .ok body)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft payloadType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.letInitialized resultType payloadType expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.letInitialized resultType payloadType expression body)
        (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_letInitialized metadata form binding lowered tailLowered,
    fault_prefix rest (.letInitializer contains form monomorphic sourceFault),
    Core.LocalSequence.letInitialized_failure resultType payloadType coreFailure⟩

theorem discard_fault
    {valueType : Core.Ty} {body : Core.Expr} {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .expression expressionId true)
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨valueType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (sourceFault : Dynamic.ExpressionFaults program context evidence source environment
      before expressionId fault after)
    (coreFailure : Core.Evaluates coreEnvironment store expression (.inLeft valueType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.discard resultType expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store (Core.LocalSequence.discard resultType expression body)
        (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_discard metadata form lowered tailLowered,
    fault_prefix rest (.expression contains form sourceFault),
    Core.LocalSequence.discard_failure resultType coreFailure⟩

theorem assign_fault
    {assignment : AssignmentResolution} {index : Nat} {payloadType : Core.Ty}
    {body : Core.Expr} {location : Core.Location} {fault : Dynamic.SemanticFault} {code : Core.Word}
    (contains : ContainsStatement source id node)
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, .unit))
    (form : node.form = .assignValue assignment .equal expressionId)
    (target : SourceCoreBasic.lowerAssignment source scope assignment .equal = .ok (index, payloadType))
    (lowered : SourceCoreBasic.lowerExpression fuel source scope expressionId reason =
      .ok ⟨payloadType, expression⟩)
    (tailLowered : SourceCoreBasic.lowerStatements fuel source scope rest resultType reason = .ok body)
    (sourceFault : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment
      before assignment.target .equal expressionId fault after)
    (lookup : coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) location))
    (coreFailure : Core.Evaluates
      (.cellRef (Core.OptionalCell.cellType payloadType) location :: coreEnvironment)
      store (expression.weakenAt 0) (.inLeft payloadType (.word code)) finalStore) :
    SourceCoreBasic.lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
        .ok (Core.LocalSequence.assign resultType (.var index) expression body) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
        (id :: rest) context (.fault fault) after ∧
      Core.Evaluates coreEnvironment store
        (Core.LocalSequence.assign resultType (.var index) expression body)
        (.inLeft resultType (.word code)) finalStore :=
  ⟨SourceCoreBasic.lowerStatements_assign metadata form target lowered tailLowered,
    fault_prefix rest (.assignValue contains form sourceFault),
    Core.LocalSequence.assign_failure resultType (.var lookup) coreFailure⟩

end Terminal

/-- A complete two-statement specimen: allocate an absent scalar/product local,
then return that local. The actual compiler emits a finite language failure;
the independent source semantics faults at precisely the new location. Any
trailing statements are ignored by the explicit return. No child evaluation or
whole-program correspondence assumption occurs in this theorem. -/
theorem uninitialized_then_return
    {program : Program} {context localContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {environment : Dynamic.Environment}
    {coreEnvironment : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    {world : Core.StoreTyping} {letId returnId : StatementId} {letNode returnNode : StatementNode}
    {binder : TypedBinder} {payloadType : Core.Ty} {readId : ExpressionId}
    (trailing : List StatementId) (reason : Core.Word)
    (unique : NodeOccurrencesUnique source)
    (letContains : ContainsStatement source letId letNode)
    (letMetadata : SourceCoreBasic.readStatement source letId = .ok (letNode, .unit))
    (letForm : letNode.form = .letDecl binder none)
    (binding : SourceCoreBasic.lowerBinder source scope binder = .ok payloadType)
    (monomorphic : binder.scheme.quantified = [])
    (extension : BinderExtends source.owner context binder localContext)
    (binderTypes : LocalCell.TypeRepresents binder.scheme.body payloadType)
    (returnContains : ContainsStatement source returnId returnNode)
    (returnMetadata : SourceCoreBasic.readStatement source returnId = .ok (returnNode, payloadType))
    (returnForm : returnNode.form = .returnStmt (some readId))
    (site : LocalCell.ReadSite source ((binder.id, payloadType) :: scope) readId payloadType)
    (readBinder : site.binder = binder.id)
    (readMetadata : SourceCoreBasic.readExpression source readId = .ok (site.node, payloadType))
    (related : LocalCell.HeapRepresents heap.cells store world) :
    let body := Core.OptionalCell.read payloadType (.var site.index) reason
    let expression := Core.LocalSequence.letUninitialized payloadType body
    let allocatedHeap : Dynamic.Heap :=
      ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩
    let allocatedStore := store ++ [Core.Value.inLeft payloadType .unit]
    SourceCoreBasic.lowerStatements 3 source scope (letId :: returnId :: trailing)
        payloadType reason = .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        (letId :: returnId :: trailing) localContext
        (.fault (.uninitializedLocation ⟨heap.cells.length⟩)) allocatedHeap ∧
      Core.Evaluates coreEnvironment store expression
        (.inLeft payloadType (.word reason)) allocatedStore ∧
      LocalCell.HeapRepresents allocatedHeap.cells allocatedStore
        (world ++ [Core.OptionalCell.cellType payloadType]) ∧
      (∀ definitions, Core.HasType (SourceCoreLocalCell.coreContext scope) expression
        (Core.LanguageResult.resultType payloadType) definitions) ∧
      ∃ required,
        (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel
          (.initial expression coreEnvironment store) =
            .done (.inLeft payloadType (.word reason)) allocatedStore) ∧
        (∀ runtimeFuel result finalStore, Core.runStateful runtimeFuel
          (.initial expression coreEnvironment store) = .done result finalStore →
            result = .inLeft payloadType (.word reason) ∧ finalStore = allocatedStore) := by
  dsimp only
  let location : Dynamic.Location := ⟨heap.cells.length⟩
  let allocatedHeap : Dynamic.Heap :=
    ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩
  have allocation : Dynamic.Heap.Allocates heap binder.scheme.body none location allocatedHeap := .append
  have indexZero : site.index = 0 := by
    have slot := site.slot
    rw [readBinder] at slot
    simp [SourceCoreLocalCell.lookup?] at slot
    exact slot.symm
  have sourceLookup : Dynamic.Environment.LooksUp ((binder.id, location) :: environment)
      site.binder location := by
    rw [readBinder]
    exact .head
  have coreLookup :
      (Core.Value.cellRef (Core.OptionalCell.cellType payloadType) location.index :: coreEnvironment)[site.index]? =
        some (.cellRef (Core.OptionalCell.cellType payloadType) location.index) := by
    rw [indexZero]
    rfl
  have coreRead : (store ++ [Core.Value.inLeft payloadType .unit]).read? location.index =
      some (.inLeft payloadType .unit) := by
    change (store ++ [Core.Value.inLeft payloadType .unit]).read? heap.cells.length = _
    rw [related.length_eq]
    simp [Core.Store.read?]
  obtain ⟨sourceFault, coreFailure⟩ := site.uninitialized program localContext evidence
    ((binder.id, location) :: environment) allocatedHeap
    (.cellRef (Core.OptionalCell.cellType payloadType) location.index :: coreEnvironment)
    (store ++ [.inLeft payloadType .unit]) location _ sourceLookup allocation.reads_new
    (binderTypes.source_unique site.types) rfl rfl coreLookup coreRead reason
  have readLowered := SourceCoreBasic.lowerExpression_local (fuel := 0) readMetadata site.form
    (site.lower unique reason)
  obtain ⟨returnLowered, returnSource, returnCore⟩ := return_fault (rest := trailing)
    returnContains returnMetadata returnForm readLowered sourceFault coreFailure
  obtain ⟨lowered, sourceFault, evaluated⟩ := letUninitialized_prefix letContains letMetadata letForm
    binding monomorphic extension binderTypes related allocation returnLowered returnSource returnCore
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨lowered, sourceFault, evaluated, (related.allocate_uninitialized binderTypes allocation).2,
    ?_, required, completes, ?_⟩
  · intro definitions
    exact Core.LocalSequence.letUninitialized_hasType (binderTypes.wellFormed definitions)
      (site.core_hasType reason definitions)
  · intro runtimeFuel result finalStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

end Solcore.SourceSemantics.CoreLowering.BasicStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BasicStatementMeaning
/-! Structural certificates for complete basic statement lists. Declarative
binder-context extensions are explicit and no execution result is assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell

theorem Metadata.read {source : TypedSource} {id : StatementId}
    {node : StatementNode} {type : Core.Ty}
    (metadata : Metadata source id node type) (unique : NodeOccurrencesUnique source) :
    SourceCoreBasic.readStatement source id = .ok (node, type) :=
  SourceCoreBasic.readStatement_eq metadata.owned
    (lookupStatement?_complete unique metadata.contains) (metadata.types.lower _)

theorem BinderCertificate.lower
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Core.Ty}
    (certificate : BinderCertificate source scope binder type) :
    SourceCoreBasic.lowerBinder source scope binder = .ok type := by
  simp [SourceCoreBasic.lowerBinder, certificate.owned, certificate.monomorphic,
    certificate.requirements, certificate.runtime, certificate.fresh,
    SourceCoreBasic.projectType, certificate.types.lower _, Except.mapError]

theorem AssignmentCertificate.lower
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {index : Nat} {type : Core.Ty}
    (certificate : AssignmentCertificate source scope assignment operator index type) :
    SourceCoreBasic.lowerAssignment source scope assignment operator = .ok (index, type) := by
  simp [SourceCoreBasic.lowerAssignment, certificate.equal, certificate.owned,
    certificate.requirements, certificate.bare, certificate.slot,
    SourceCoreBasic.projectType, certificate.types.lower _, Except.mapError,
    SourceCoreBasic.ensureType, bind, Except.bind, pure, Pure.pure, Except.pure]

/-- A structural statement certificate additionally carries the declarative
source binder-context extensions. None of its fields assumes compilation or
evaluation. The static context requirement is intentionally not inferred from
the basic compiler's lexical scope checks. -/
inductive Tree (source : TypedSource) (reason : Core.Word) :
    SourceCoreLocalCell.Scope → Context → List StatementId → Core.Ty → Core.Expr → Nat → Prop where
  | nil {scope context} :
      Tree source reason scope context [] .unit (Core.LanguageResult.success .unit) 0
  | letUninitialized
      {scope context middleContext id rest node binder payloadType resultType body depth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree source reason ((binder.id, payloadType) :: scope) middleContext
        rest resultType body depth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.letUninitialized payloadType body) (depth + 1)
  | letInitialized
      {scope context middleContext id rest node binder payloadType resultType
        initializer initializerCode body initializerDepth bodyDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder (some initializer))
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : BasicExpressions.Tree source scope reason initializer payloadType initializerCode initializerDepth)
      (tail : Tree source reason ((binder.id, payloadType) :: scope) middleContext
        rest resultType body bodyDepth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.letInitialized resultType payloadType initializerCode body)
        (max initializerDepth bodyDepth + 1)
  | assign
      {scope context id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth bodyDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : BasicExpressions.Tree source scope reason rhs payloadType rhsCode rhsDepth)
      (tail : Tree source reason scope context rest resultType body bodyDepth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.assign resultType (.var index) rhsCode body) (max rhsDepth bodyDepth + 1)
  | discard
      {scope context id rest node valueId valueType resultType valueCode body valueDepth bodyDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .expression valueId true)
      (value : BasicExpressions.Tree source scope reason valueId valueType valueCode valueDepth)
      (tail : Tree source reason scope context rest resultType body bodyDepth) :
      Tree source reason scope context (id :: rest) resultType
        (Core.LocalSequence.discard resultType valueCode body) (max valueDepth bodyDepth + 1)
  | returnValue
      {scope context id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : BasicExpressions.Tree source scope reason valueId resultType valueCode valueDepth) :
      Tree source reason scope context (id :: rest) resultType valueCode (valueDepth + 1)
  | returnUnit {scope context id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree source reason scope context (id :: rest) .unit (Core.LanguageResult.success .unit) 1
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : BasicExpressions.Tree source scope reason valueId resultType valueCode valueDepth) :
      Tree source reason scope context [id] resultType valueCode (valueDepth + 1)

theorem Tree.cellPayload
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) : Core.CellPayload type := by
  induction tree with
  | nil | returnUnit => exact .unit
  | returnValue _ _ _ value | tailExpression _ _ value => exact value.cellPayload
  | letUninitialized _ _ _ _ _ ih | letInitialized _ _ _ _ _ _ ih
  | assign _ _ _ _ _ ih | discard _ _ _ _ ih => exact ih

theorem Tree.hasType
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LanguageResult.resultType type) := by
  induction tree with
  | nil | returnUnit => exact Core.LanguageResult.success_hasType .unit
  | returnValue _ _ _ value | tailExpression _ _ value => exact value.hasType
  | letUninitialized _ _ binding _ _ ih =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) ih
  | letInitialized _ _ _ _ value tail ih =>
      exact Core.LocalSequence.letInitialized_hasType tail.cellPayload.wellFormed value.hasType ih
  | assign _ _ target value tail ih =>
      exact Core.LocalSequence.assign_hasType tail.cellPayload.wellFormed
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType ih
  | discard _ _ value tail ih =>
      exact Core.LocalSequence.discard_hasType tail.cellPayload.wellFormed value.hasType ih

theorem Tree.lower
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreBasic.lowerStatements fuel source scope statements type reason = .ok code := by
  induction tree generalizing fuel with
  | nil => exact SourceCoreBasic.lowerStatements_nil fuel source _ reason
  | letUninitialized metadata form binding _ _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_letUninitialized
            (metadata.read unique) form binding.lower (ih fuel (by omega))
  | letInitialized metadata form binding _ value _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_letInitialized
            (metadata.read unique) form binding.lower (value.lower unique fuel (by omega)) (ih fuel (by omega))
  | assign metadata form target value _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_assign
            (metadata.read unique) form target.lower (value.lower unique fuel (by omega)) (ih fuel (by omega))
  | discard metadata form value _ ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_discard
            (metadata.read unique) form (value.lower unique fuel (by omega)) (ih fuel (by omega))
  | returnValue _ metadata form value =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_return
            (metadata.read unique) form (value.lower unique fuel (by omega))
  | returnUnit _ metadata form =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_returnUnit (metadata.read unique) form
  | tailExpression metadata form value =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreBasic.lowerStatements_tail
            (metadata.read unique) form (value.lower unique fuel (by omega))


inductive OutcomeRepresents (world : Core.StoreTyping) (reason : Core.Word) :
    Core.Ty → Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough {scope environment coreEnvironment}
      (environments : EnvRepresents world scope environment coreEnvironment) :
      OutcomeRepresents world reason .unit (.fallthrough environment) (.inRight .word .unit)
  | returned (value : SourceStagedValue.Value) {type : Core.Ty}
      (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents world reason type (.returned (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (location : Dynamic.Location) (type : Core.Ty) :
      OutcomeRepresents world reason type (.fault (.uninitializedLocation location))
        (.inLeft type (.word reason))

private theorem staged_runtime_type (value : SourceStagedValue.Value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .pair left right

private theorem weaken_three
    {environment : Core.Environment} {context : Core.Context} {store finalStore : Core.Store}
    {world finalWorld : Core.StoreTyping} {expression : Core.Expr} {result : Core.Value}
    {resultType referenceType valueType : Core.Ty} {reference value : Core.Value}
    (evaluation : Core.Evaluates environment store expression result finalStore)
    (typing : Core.HasType context expression (Core.LanguageResult.resultType resultType))
    (payload : Core.CellPayload resultType)
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment context)
    (storeTyped : Core.RuntimeStoreHasTypes world store)
    (finalTyped : Core.StoreHasTypes finalWorld finalStore)
    (referenceTyped : Core.RuntimeValueHasType world reference referenceType)
    (valueTyped : Core.RuntimeValueHasType world value valueType) :
    Core.Evaluates (.unit :: value :: reference :: environment) store
      (((expression.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore := by
  have first := evaluation.weakenAt_zero_cellPayload typing (.sum .word payload)
    environmentTyped storeTyped finalTyped reference
  have firstTyped : Core.HasType (referenceType :: context) (expression.weakenAt 0)
      (Core.LanguageResult.resultType resultType) := by
    simpa [Core.Context.insertAt] using typing.weakenAt (inserted := referenceType) 0
  have second := first.weakenAt_zero_cellPayload firstTyped (.sum .word payload)
    (.cons referenceTyped environmentTyped) storeTyped finalTyped value
  have secondTyped : Core.HasType (valueType :: referenceType :: context)
      ((expression.weakenAt 0).weakenAt 0) (Core.LanguageResult.resultType resultType) := by
    simpa [Core.Context.insertAt] using firstTyped.weakenAt (inserted := valueType) 0
  exact second.weakenAt_zero_cellPayload secondTyped (.sum .word payload)
    (.cons valueTyped (.cons referenceTyped environmentTyped)) storeTyped finalTyped .unit

/-- Whole-list preservation for the structural basic fragment. Child evaluation
and final-store typing are derived recursively. The only heap premise is the
initial scalar/product optional-cell representation. -/
theorem Tree.preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ finalContext outcome after result finalStore finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalWorld reason type outcome result ∧
      Core.Evaluates coreEnvironment store code result finalStore ∧
      HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends world finalWorld := by
  induction tree generalizing environment heap coreEnvironment store world with
  | nil =>
      exact ⟨_, _, _, _, _, _, .control .nil, .fallthrough environments,
        .inRight .unit, heaps, .refl _⟩
  | @returnUnit scope context id node rest metadata form =>
      obtain ⟨_, sourceExecution, coreExecution⟩ := returnUnit_prefix (fuel := 0)
        (scope := scope) (reason := reason) metadata.contains (metadata.read unique) form
      exact ⟨_, _, _, _, _, _, sourceExecution, .returned .unit rfl, coreExecution, heaps, .refl _⟩
  | @returnValue scope context id node valueId resultType valueCode valueDepth rest metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_prefix staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @tailExpression scope context id node valueId resultType valueCode valueDepth metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := Solcore.SourceSemantics.CoreLowering.BasicStatements.tailExpression staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := tailExpression_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @letUninitialized scope context middleContext id rest node binder payloadType resultType body bodyDepth
      metadata form binding extension tail ih =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
      obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
        tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih nextEnvironments nextHeaps
      obtain ⟨_, sourceExecution, coreExecution⟩ := letUninitialized_prefix metadata.contains
        (metadata.read unique) form binding.lower binding.monomorphic extension binding.types heaps allocated
        (tail.lower unique bodyDepth (Nat.le_refl _)) tailSource tailCore
      exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended)⟩
  | @letInitialized scope context middleContext id rest node binder payloadType resultType
      initializer initializerCode body initializerDepth bodyDepth metadata form binding extension value tail ih =>
      let fuel := max initializerDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              have binderType : binder.scheme.body = SourceStagedValue.sourceType staged :=
                binding.types.source_unique (typed ▸ stagedTypes staged)
              have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
                  ⟨heap.cells.length⟩
                  ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
              have cell : CellRepresents
                  { type := binder.scheme.body, value := some (StagedValue.toSource staged) }
                  (.inRight .unit (SourceStagedValue.toCore staged)) payloadType := by
                rw [binderType, ← typed]
                exact .initialized staged
              obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
              obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih nextEnvironments nextHeaps
              have shifted := tailCore.weakenAt_cellPayload tail.hasType (.sum .word tail.cellPayload)
                (nextEnvironments.runtime_hasTypes []) (nextHeaps.runtime_hasTypes [])
                finalHeaps.firstOrder_hasTypes 1 (SourceStagedValue.toCore staged)
              simp only [Core.Environment.insertAt] at shifted
              obtain ⟨_, sourceExecution, coreExecution⟩ := letInitialized_prefix staged metadata.contains
                (metadata.read unique) form (typed ▸ binding.lower) binding.monomorphic extension binderType
                (typed ▸ valueLowered) sourceEvaluation coreEvaluation heaps allocated
                (typed ▸ tailLowered) tailSource (typed ▸ shifted)
              exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, typed ▸ coreExecution, finalHeaps,
                (Core.WorldExtends.trans ⟨_, rfl⟩ extended)⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := letInitialized_fault metadata.contains
                (metadata.read unique) form binding.lower binding.monomorphic valueLowered tailLowered
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @discard scope context id rest node valueId valueType resultType valueCode body valueDepth bodyDepth
      metadata form value tail ih =>
      let fuel := max valueDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih environments heaps
              have shifted := tailCore.weakenAt_zero_cellPayload tail.hasType (.sum .word tail.cellPayload)
                (environments.runtime_hasTypes []) (heaps.runtime_hasTypes [])
                finalHeaps.firstOrder_hasTypes (SourceStagedValue.toCore staged)
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_prefix staged metadata.contains
                (metadata.read unique) form valueLowered sourceEvaluation coreEvaluation tailLowered tailSource shifted
              exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, extended⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_fault metadata.contains
                (metadata.read unique) form valueLowered tailLowered sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩
  | @assign scope context id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth bodyDepth
      metadata form target value tail ih =>
      let fuel := max rhsDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        value.preserves program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨location, updatedHeap, updatedStore, assignmentSource, lookup, ⟨oldValue, readable⟩,
                written, updatedHeaps, updatedEnvironments⟩ := equal_assignment environments heaps (.refl _) heaps
                  target.slot target.bare staged typed sourceEvaluation
              obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, extended⟩ := ih updatedEnvironments updatedHeaps
              have rhsShifted := coreEvaluation.weakenAt_zero_cellPayload value.hasType
                (.sum .word value.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (.cellRef (Core.OptionalCell.cellType payloadType) location.index)
              have referenceTyped : Core.RuntimeValueHasType world
                  (.cellRef (Core.OptionalCell.cellType payloadType) location.index)
                  (Core.OptionalCell.referenceType payloadType) := by
                obtain ⟨reference, found, referenceTyping⟩ :=
                  (environments.runtime_hasTypes []).lookup (SourceCoreLocalCell.lookup?_context target.slot)
                rw [lookup] at found
                cases found
                exact referenceTyping
              have shifted := weaken_three tailCore tail.hasType tail.cellPayload
                (updatedEnvironments.runtime_hasTypes []) (updatedHeaps.runtime_hasTypes [])
                finalHeaps.firstOrder_hasTypes referenceTyped (staged_runtime_type staged world)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_prefix metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered assignmentSource
                lookup rhsShifted readable written tailSource shifted
              exact ⟨_, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, extended⟩
      | uninitialized location =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨targetLocation, cell, current, sourceLookup, coreLookup, _, read, _, cellRelated⟩ :=
                environments.lookup_heap heaps target.slot
              let captured : Dynamic.ResolvedPlace := {
                location := targetLocation, rootType := cell.type, valueType := assignment.target.type,
                projections := [], selected := cell.value
              }
              have resolved : Dynamic.SourcePlaceResolves program context evidence source environment
                  heap assignment.target captured heap := by
                apply Dynamic.SourcePlaceResolves.intro sourceLookup read
                · rw [target.bare]; exact .nil
                · exact read
                · exact cellRelated.rootInitialValue
                · exact .nil
              have rhsShifted := coreEvaluation.weakenAt_zero_cellPayload value.hasType
                (.sum .word value.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (.cellRef (Core.OptionalCell.cellType payloadType) targetLocation.index)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_fault metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered
                (.rhs resolved sourceFault) coreLookup rhsShifted
              exact ⟨_, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _⟩

/-- The finite basic grammar supplies its evaluation witness structurally.
Successful Core runs agree on the result and complete final store. This does
not assert determinism or completeness of every source fault rule. -/
theorem Tree.lower_run_preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (compilationFuel : Nat) (enough : depth ≤ compilationFuel)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    SourceCoreBasic.lowerStatements compilationFuel source scope statements type reason = .ok code ∧
    Core.infer? (SourceCoreLocalCell.coreContext scope) code = some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalWorld reason type outcome result ∧
      HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends world finalWorld ∧
      EnvRepresents finalWorld scope environment coreEnvironment ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) =
        .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment store) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) := by
  obtain ⟨finalContext, outcome, after, result, finalStore, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, extended⟩ :=
    tree.preserves unique program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨tree.lower unique compilationFuel enough, Core.infer_complete tree.hasType,
    finalContext, outcome, after, result, finalStore, finalWorld, required,
    sourceExecution, related, finalHeaps, extended, environments.extend extended, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

end Solcore.SourceSemantics.CoreLowering.BasicStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralStatements
/-! Whole basic statement-list correspondence over mapped source cells and
administrative Core cells. The structural statement certificate includes the
source binder-context extensions; it assumes neither child evaluation nor
whole-list evaluation. Extracting those context extensions from arbitrary
successful statement lowering remains a separate obligation. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.GeneralStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- Basic statements may change the heap, but never construct or call a Core
closure. This static restriction permits exact temporary-binder insertion. -/
theorem heapEffects {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) : Core.HeapEffects.Expression code := by
  induction tree with
  | nil | returnUnit => exact .inRight .unit
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact .of_readOnly (GeneralExpressions.Basic.readOnly value)
  | letUninitialized _ _ _ _ _ tail => exact .letE (.newCell (.inLeft .unit)) tail
  | letInitialized _ _ _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Basic.readOnly value)) (.inLeft .var)
        (.letE (.newCell (.inRight .var)) (tail.weakenAt 1))
  | assign _ _ _ value _ tail =>
      exact .letE .var
        (.caseE ((Core.HeapEffects.Expression.of_readOnly (GeneralExpressions.Basic.readOnly value)).weakenAt 0)
          (.inLeft .var) (.letE (.storeCell .var (.inRight .var)) (((tail.weakenAt 0).weakenAt 0).weakenAt 0)))
  | discard _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Basic.readOnly value)) (.inLeft .var) (tail.weakenAt 0)

inductive OutcomeRepresents (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (administrativeContext : Core.Context) (reason : Core.Word) :
    Core.Ty → Dynamic.ControlOutcome → Core.Value → Prop where
  | fallthrough {scope environment coreEnvironment}
      (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
      OutcomeRepresents mapping world administrativeContext reason .unit (.fallthrough environment) (.inRight .word .unit)
  | returned (value : SourceStagedValue.Value) {type : Core.Ty}
      (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents mapping world administrativeContext reason type (.returned (StagedValue.toSource value))
        (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (location : Dynamic.Location) (type : Core.Ty) :
      OutcomeRepresents mapping world administrativeContext reason type (.fault (.uninitializedLocation location))
        (.inLeft type (.word reason))

private theorem weaken_three {environment : Core.Environment} {store finalStore : Core.Store}
    {expression : Core.Expr} {result : Core.Value}
    (restricted : Core.HeapEffects.Expression expression)
    (evaluation : Core.Evaluates environment store expression result finalStore) (reference value : Core.Value) :
    Core.Evaluates (.unit :: value :: reference :: environment) store
      (((expression.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore :=
  (((restricted.weakenAt 0).weakenAt 0).evaluation_weakenAt_zero
    ((restricted.weakenAt 0).evaluation_weakenAt_zero
      (restricted.evaluation_weakenAt_zero evaluation reference) value) .unit)

private theorem cellsWrite_set {cells : List Dynamic.Cell} {index : Nat}
    {previous : Dynamic.Cell} (selected : Dynamic.Heap.CellAt cells index previous)
    (replacement : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite cells index replacement (cells.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

/-- Basic expression RHS evaluation leaves its heap unchanged. The captured
source location and independently mapped Core location identify the same cell. -/
private theorem equal_assignment
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {target : PlaceResolution} {rhs : ExpressionId} {index : Nat} {payloadType : Core.Ty}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (slot : SourceCoreLocalCell.lookup? scope target.root = some (index, payloadType))
    (bare : target.projections = []) (value : SourceStagedValue.Value)
    (valueType : SourceStagedValue.coreType value = payloadType)
    (rhsEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment
      heap rhs (StagedValue.toSource value) heap) :
    ∃ (coreLocation : Core.Location) (after : Dynamic.Heap) (finalStore : Core.Store),
      Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies .equal) environment heap target rhs (StagedValue.toSource value) after ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) ∧
      (∃ oldValue, store.read? coreLocation = some oldValue) ∧
      store.write? coreLocation (.inRight .unit (SourceStagedValue.toCore value)) = some finalStore ∧
      GeneralHeap.HeapRepresents mapping world after finalStore ∧
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨location, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
    environments.lookup_heap heaps slot
  let replacement : Dynamic.Cell := { cell with value := some (StagedValue.toSource value) }
  let after : Dynamic.Heap := ⟨heap.cells.set location.index replacement⟩
  have sourceWrite : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after := by
    cases read with
    | intro selected => exact .intro (.intro selected) (cellsWrite_set selected replacement)
  obtain ⟨finalStore, written, heapRelated⟩ := heaps.write_initialized reference value valueType sourceWrite
  let captured : Dynamic.ResolvedPlace := {
    location, rootType := cell.type, valueType := target.type, projections := [], selected := cell.value
  }
  have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap target captured heap := by
    apply Dynamic.SourcePlaceResolves.intro lookup read
    · rw [bare]; exact .nil
    · exact read
    · exact represented.rootInitialValue
    · exact .nil
  exact ⟨coreLocation, after, finalStore,
    .intro resolved rhsEvaluated
      (.intro read rfl represented.rootInitialValue (.leaf (.equal cell.value (StagedValue.toSource value))) sourceWrite),
    coreLookup, ⟨stored, coreRead⟩, written, heapRelated, environments,
    GeneralHeap.AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) written⟩

private theorem prepend
    {program : Program} {context middleContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment nextEnvironment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id
      middleContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program middleContext evidence source
      nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
      (id :: rest) finalContext outcome after := by
  cases rest with
  | nil =>
      cases tail with
      | control execute =>
          cases execute
          exact .control (.singleton contains notTail head)
      | fault fault => cases fault
  | cons next rest =>
      cases tail with
      | control execute => exact .control (.cons head execute)
      | fault fault => exact .fault (.tail head fault)

theorem preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalMapping finalWorld administrativeContext reason type outcome result ∧
      Core.Evaluates coreEnvironment store code result finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore := by
  induction tree generalizing environment heap coreEnvironment store world mapping with
  | nil =>
      exact ⟨_, _, _, _, _, _, _, .control .nil, .fallthrough environments,
        .inRight .unit, heaps, .refl _, .refl _, .refl _ _⟩
  | @returnUnit scope context id node rest metadata form =>
      obtain ⟨_, sourceExecution, coreExecution⟩ := returnUnit_prefix (fuel := 0)
        (scope := scope) (reason := reason) metadata.contains (metadata.read unique) form
      exact ⟨_, _, _, _, _, _, _, sourceExecution, .returned .unit rfl, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @returnValue scope context id node valueId resultType valueCode valueDepth rest metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_prefix staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := return_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @tailExpression scope context id node valueId resultType valueCode valueDepth metadata form value =>
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := Solcore.SourceSemantics.CoreLowering.BasicStatements.tailExpression staged metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceEvaluation coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .returned staged typed, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := tailExpression_fault metadata.contains
                (metadata.read unique) form (value.lower unique valueDepth (Nat.le_refl _))
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @letUninitialized scope context middleContext id rest node binder payloadType resultType body bodyDepth
      metadata form binding extension tail ih =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
      obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
        tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih nextEnvironments nextHeaps
      have sourceExecution := prepend metadata.contains
        (by intro expression; rw [form]; intro impossible; cases impossible)
        (.letUninitialized metadata.contains form binding.monomorphic extension allocated) tailSource
      have coreExecution := Core.LocalSequence.letUninitialized_evaluates payloadType tailCore
      exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps,
        GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
        GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
  | @letInitialized scope context middleContext id rest node binder payloadType resultType
      initializer initializerCode body initializerDepth bodyDepth metadata form binding extension value tail ih =>
      let fuel := max initializerDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              have binderType : binder.scheme.body = SourceStagedValue.sourceType staged :=
                binding.types.source_unique (typed ▸ stagedTypes staged)
              have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
                  ⟨heap.cells.length⟩
                  ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
              have cell : CellRepresents
                  { type := binder.scheme.body, value := some (StagedValue.toSource staged) }
                  (.inRight .unit (SourceStagedValue.toCore staged)) payloadType := by
                rw [binderType, ← typed]
                exact .initialized staged
              obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih nextEnvironments nextHeaps
              have shifted := (heapEffects tail).evaluation_weakenAt tailCore 1 (SourceStagedValue.toCore staged)
              simp only [Core.Environment.insertAt] at shifted
              have sourceExecution := prepend metadata.contains
                (by intro expression; rw [form]; intro impossible; cases impossible)
                (.letInitialized metadata.contains form sourceEvaluation binding.monomorphic extension allocated) tailSource
              have coreExecution := Core.LocalSequence.letInitialized_success resultType payloadType coreEvaluation shifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps,
                GeneralHeap.LocationMap.Extends.trans ⟨_, rfl⟩ mapsExtended,
        (Core.WorldExtends.trans ⟨_, rfl⟩ extended),
        GeneralHeap.AdministrativePreserved.trans (GeneralHeap.AdministrativePreserved.allocate _ _ _) tailFrame⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := letInitialized_fault metadata.contains
                (metadata.read unique) form binding.lower binding.monomorphic valueLowered tailLowered
                sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @discard scope context id rest node valueId valueType resultType valueCode body valueDepth bodyDepth
      metadata form value tail ih =>
      let fuel := max valueDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih environments heaps
              have shifted := (heapEffects tail).evaluation_weakenAt_zero tailCore (SourceStagedValue.toCore staged)
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_prefix staged metadata.contains
                (metadata.read unique) form valueLowered sourceEvaluation coreEvaluation tailLowered tailSource shifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, mapsExtended, extended, tailFrame⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨_, sourceExecution, coreExecution⟩ := discard_fault metadata.contains
                (metadata.read unique) form valueLowered tailLowered sourceFault coreEvaluation
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩
  | @assign scope context id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth bodyDepth
      metadata form target value tail ih =>
      let fuel := max rhsDepth bodyDepth
      have valueLowered := value.lower unique fuel (Nat.le_max_left _ _)
      have tailLowered := tail.lower unique fuel (Nat.le_max_right _ _)
      obtain ⟨sourceOutcome, result, sourceEvaluation, related, coreEvaluation⟩ :=
        GeneralExpressions.Basic.preserves value program context evidence environments heaps
      cases related with
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨coreLocation, updatedHeap, updatedStore, assignmentSource, lookup, ⟨oldValue, readable⟩,
                written, updatedHeaps, updatedEnvironments, updatedFrame⟩ := equal_assignment environments heaps
                  target.slot target.bare staged typed sourceEvaluation
              obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
                tailSource, tailRelated, tailCore, finalHeaps, mapsExtended, extended, tailFrame⟩ := ih updatedEnvironments updatedHeaps
              have rhsShifted := (GeneralExpressions.Basic.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation)
              have shifted := weaken_three (heapEffects tail) tailCore
                (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) (SourceStagedValue.toCore staged)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_prefix metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered assignmentSource
                lookup rhsShifted readable written tailSource shifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, tailRelated, coreExecution, finalHeaps, mapsExtended, extended,
                GeneralHeap.AdministrativePreserved.trans updatedFrame tailFrame⟩
      | uninitialized faultSite location provenance =>
          cases sourceEvaluation with
          | fault sourceFault =>
              obtain ⟨targetLocation, coreTarget, cell, current, sourceLookup, coreLookup, _, read, _, cellRelated⟩ :=
                environments.lookup_heap heaps target.slot
              let captured : Dynamic.ResolvedPlace := {
                location := targetLocation, rootType := cell.type, valueType := assignment.target.type,
                projections := [], selected := cell.value
              }
              have resolved : Dynamic.SourcePlaceResolves program context evidence source environment
                  heap assignment.target captured heap := by
                apply Dynamic.SourcePlaceResolves.intro sourceLookup read
                · rw [target.bare]; exact .nil
                · exact read
                · exact cellRelated.rootInitialValue
                · exact .nil
              have rhsShifted := (GeneralExpressions.Basic.readOnly value).evaluation_weakenAt_zero coreEvaluation
                (.cellRef (Core.OptionalCell.cellType payloadType) coreTarget)
              obtain ⟨_, sourceExecution, coreExecution⟩ := assign_fault metadata.contains
                (metadata.read unique) form target.lower valueLowered tailLowered
                (.rhs resolved sourceFault) coreLookup rhsShifted
              exact ⟨_, _, _, _, _, _, _, sourceExecution, .uninitialized location _, coreExecution, heaps, .refl _, .refl _, .refl _ _⟩

theorem hasType {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth) (administrativeContext : Core.Context) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code (Core.LanguageResult.resultType type) := by
  have respects : Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
    intro index foundType found
    change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simpa using tree.hasType.rename respects

/-- A static Tree supplies the actual compiler equation and finite execution.
It also preserves initial captures, existing administrative code cells, and
both representation extensions. This is not certificate extraction from an
arbitrary successful statement compiler call. -/
theorem lower_run_preserves
    {source : TypedSource} {reason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source reason scope context statements type code depth)
    (unique : NodeOccurrencesUnique source) (compilationFuel : Nat) (enough : depth ≤ compilationFuel)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    SourceCoreBasic.lowerStatements compilationFuel source scope statements type reason = .ok code ∧
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code =
      some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      OutcomeRepresents finalMapping finalWorld administrativeContext reason type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) =
        .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment store) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) := by
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, finalHeaps, mapsExtended, worldsExtended, administrativePreserved⟩ :=
    preserves tree unique program evidence environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreExecution
  refine ⟨tree.lower unique compilationFuel enough, Core.infer_complete (hasType tree administrativeContext),
    finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, finalHeaps, mapsExtended, worldsExtended,
    environments.extend mapsExtended worldsExtended, administrativePreserved, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreExecution

end Solcore.SourceSemantics.CoreLowering.GeneralStatements
end
