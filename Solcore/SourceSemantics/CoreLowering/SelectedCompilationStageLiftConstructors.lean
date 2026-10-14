import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates

/-! Actual tuple and nominal-constructor traces lift through the original
ordered compiler argument tree. Successful values and semantic failures keep
their ordinary endpoint; a rejected child retains its exact reached heap. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) : stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [sourceType, ih rest]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}

theorem tuple (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨actualTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique metadata.found form metadata.coercions typed
  cases tree_types sequence unique typing
  have occurrence : Staging.Recursive.Occurrence invocation expression (.tuple ids) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  obtain ⟨childSize, sourceOutcome, childTrace, packed, smaller⟩ :=
    CompatibleExpressionTuples.source_inv_at metadata form unique execution
  cases packed with
  | values pack =>
    cases childTrace with
    | values evaluated =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted evaluated (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .tupleValue occurrence trace pack, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .tupleFault occurrence trace, .rejected origin call reason _⟩
  | fault reason =>
    cases childTrace with
    | fault failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted failed (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .tupleFault occurrence trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .tupleFault occurrence trace, .rejected origin call reason _⟩

theorem constructor (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {ids : List ExpressionId}
    {instantiation : DataConstructorInstantiation} {codes : List SourceCoreBasic.LoweredExpr}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .constructor instantiation ids) (unique : NodeOccurrencesUnique invocation.source)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation expression (.constructor instantiation ids) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  obtain ⟨childSize, sourceOutcome, childTrace, packed, smaller⟩ :=
    RecursiveNamedDataExpressionSourceBounds.constructor_inv metadata form unique valid execution
  cases packed with
  | values sources =>
    cases childTrace with
    | values evaluated =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted evaluated (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .constructorValue occurrence valid trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .constructorFault occurrence trace, .rejected origin call reason _⟩
  | fault reason =>
    cases childTrace with
    | fault failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted failed (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .constructorFault occurrence trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .constructorFault occurrence trace, .rejected origin call reason _⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
