import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.DataPlaceExecution

/-! Universal child meanings under execute's real temporary binders. These
lemmas instantiate the semantic induction hypothesis; static certificates do
not contain executions of keys, RHS expressions or continuation bodies.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open SourceCoreDataPlaces

def prefixRenaming : Nat → Renaming → Renaming
  | 0, ξ => ξ
  | count + 1, ξ => Renaming.comp (Renaming.insertion 0) (prefixRenaming count ξ)

theorem shift_succ (count : Nat) (expression : Expr) :
    shift (count + 1) expression = (shift count expression).weakenAt 0 := by
  simp [shift, List.range_succ, List.foldl_append]

theorem rename_prefix (expression : Expr) (count : Nat) (ξ : Renaming) :
    expression.rename (prefixRenaming count ξ) = shift count (expression.rename ξ) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [prefixRenaming, GenericExpressionMeaning.rename_prefix, ih, shift_succ]

theorem prefix_agrees {canonical actual : Environment} {ξ : Renaming}
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual) (slots : Environment) :
    ReadOnly.EnvironmentsAgree (prefixRenaming slots.length ξ) canonical (slots ++ actual) := by
  induction slots with
  | nil => exact layout
  | cons value rest ih => exact agree_prefix ih value

/-- This applies equally to the one key reference binder, the three RHS
binders and the seven post-write binders. Existing closure captures are kept;
no exact-value evaluation weakening principle is used. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Preserves model program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual) (slots : Environment)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (slots ++ actual) store (shift slots.length (lowered.expression.rename ξ)) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    meaning generated found environments heaps locals (prefix_agrees layout slots) trace
  exact ⟨value, finalStore, finalMap, finalWorld, by simpa only [rename_prefix] using evaluated, rest⟩

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Reflects model program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual) (slots : Environment)
    (evaluated : Evaluates (slots ++ actual) store
      (shift slots.length (lowered.expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply meaning generated found environments heaps locals (prefix_agrees layout slots)
  simpa only [rename_prefix] using evaluated

/-- A fault from the actual index vector completes the whole emitted
assignment with that fault. Getter, RHS, modifier, setter and continuation
are absent from the assumptions and are skipped by the proved evaluation. -/
theorem keys_fault {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {model : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep}
    (meaning : Preserves model program context evidence source certificate faults)
    {assignment : AssignmentResolution} {site : SourceCoreElaboration.ErrorSite} {fuel : Nat}
    {route : Route} {prepared : Prepared} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    {expression : ExpressionLowerer} {reasonAt : ExpressionId → Word} {codes : List SourceCoreBasic.LoweredExpr}
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalidProjection missing = .ok prepared)
    (generated : ListRel (DataPlaceCertificates.KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before assignment.target.projections reason after)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, tree, _⟩ := DataPlaceKeyOrder.tree_of_generated_keys described preparedBy generated extract
  obtain ⟨target, coreLookup, _⟩ := environments.lookup_visible lookup slot
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v found; exact found
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    DataPlaceKeyOrder.preserves_fault tree meaning environments heaps locals
      (prefix_agrees layout [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) trace
  have keysEvaluated : Evaluates
      (DataPlaceExecution.referenceEnvironment prepared.route.rootType target coreEnvironment) store
      (shift 1 (SourceCoreCalls.packArguments codes).expression)
      (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore := by
    simpa only [rename_prefix, Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append, DataPlaceExecution.referenceEnvironment] using evaluated
  exact ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace),
    DataPlaceExecution.execute_keys_failure (.var coreLookup) keysEvaluated, rest⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions
