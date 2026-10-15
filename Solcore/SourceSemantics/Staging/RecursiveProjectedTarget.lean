import Solcore.SourceSemantics.Staging.RecursiveBareBitNot

/-! Ordered projection keys and pure snapshots for staged projected writes.
Key expressions run before the getter. The final write retains the snapshot
while reconstructing the path from the root reached after the RHS. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- Members have no expression child; every index occurrence stays in order. -/
def keys : List PlaceProjection → List ExpressionId
  | [] => []
  | .member _ _ :: rest => keys rest
  | .index key :: rest => key :: keys rest

inductive Values : List PlaceProjection → List Dynamic.Value → List EvaluatedProjection → Prop where
  | nil : Values [] [] []
  | member {name index rest values evaluated} (tail : Values rest values evaluated) :
      Values (.member name index :: rest) values (.member name index :: evaluated)
  | index {key rest value values evaluated} (tail : Values rest values evaluated) :
      Values (.index key :: rest) (value :: values) (.index value :: evaluated)

/-- Root lookup and the first read precede all key effects. -/
inductive RootReady (environment : Environment) (heap : Heap) (place : PlaceResolution) : Prop where
  | intro {location cell}
      (lookup : Environment.LooksUp environment place.root location)
      (read : Heap.Reads heap location cell) : RootReady environment heap place

inductive RootFault (environment : Environment) (heap : Heap) (place : PlaceResolution) : SemanticFault → Prop where
  | unbound (missing : environment.Unbound place.root) : RootFault environment heap place (.unboundLocal place.root)
  | dangling {location} (lookup : Environment.LooksUp environment place.root location)
      (missing : heap.Dangling location) : RootFault environment heap place (.danglingLocation location)

/-- The second root read and pure getter use the actual heap after all keys. -/
inductive Snapshot (environment : Environment) (before after : Heap) (place : PlaceResolution)
    (values : List Dynamic.Value) : ResolvedPlace → Prop where
  | intro {location initialCell currentCell evaluated initial selected}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (currentRead : Heap.Reads after location currentCell)
      (initialValue : RootInitialValue currentCell initial)
      (selection : ProjectionsRead initial evaluated selected) :
      Snapshot environment before after place values
        { location := location, rootType := currentCell.type, valueType := place.type,
          projections := evaluated, selected := selected }

/-- Getter failures occur only after the complete successful key row. -/
inductive GetterFault (environment : Environment) (before after : Heap) (place : PlaceResolution)
    (values : List Dynamic.Value) : SemanticFault → Prop where
  | dangling {location initialCell evaluated}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (missing : after.Dangling location) : GetterFault environment before after place values (.danglingLocation location)
  | projection {location initialCell currentCell evaluated initial reason}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (currentRead : Heap.Reads after location currentCell)
      (initialValue : RootInitialValue currentCell initial)
      (fault : ProjectionsFaults initial evaluated reason) : GetterFault environment before after place values reason
  | uninitialized {location initialCell currentCell evaluated}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (currentRead : Heap.Reads after location currentCell)
      (empty : currentCell.value = none)
      (notMapping : ¬ ∃ keyType valueType, currentCell.type = .mapping keyType valueType)
      (nonempty : evaluated ≠ []) : GetterFault environment before after place values (.uninitializedLocation location)

/-- The latest root path is checked before the saved-snapshot leaf modifier. -/
inductive WriteFault (operator : Syntax.ValueAssignOp) (target : ResolvedPlace)
    (right : Dynamic.Value) (heap : Heap) : SemanticFault → Prop where
  | operands {currentCell initial currentSelected}
      (currentRead : Heap.Reads heap target.location currentCell)
      (rootType : currentCell.type = target.rootType)
      (initialValue : RootInitialValue currentCell initial)
      (pathRead : ProjectionsRead initial target.projections currentSelected)
      (invalid : AssignmentOperandsInvalid operator target.selected right) :
      WriteFault operator target right heap (.invalidAssignmentOperands operator)
  | structural {currentCell initial reason}
      (currentRead : Heap.Reads heap target.location currentCell)
      (rootType : currentCell.type = target.rootType)
      (initialValue : RootInitialValue currentCell initial)
      (fault : ProjectionsFaults initial target.projections reason) :
      WriteFault operator target right heap reason

theorem Values.evaluates {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {projections : List PlaceProjection}
    {values : List Dynamic.Value} {evaluated : List EvaluatedProjection}
    (ordered : Values projections values evaluated)
    (trace : ExpressionsEvaluate program context evidence source environment before (keys projections) values after) :
    SourceProjectionsEvaluate program context evidence source environment before projections evaluated after := by
  induction ordered generalizing before with
  | nil => cases trace; exact .nil
  | member _ ih => exact .member (ih trace)
  | index _ ih =>
      cases trace with
      | cons head tail => exact .index head (ih tail)

theorem keys_fault {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {projections : List PlaceProjection} {reason : SemanticFault}
    (trace : ExpressionsFault program context evidence source environment before (keys projections) reason after) :
    SourceProjectionsFault program context evidence source environment before projections reason after := by
  induction projections generalizing before with
  | nil => cases trace
  | cons projection rest ih =>
      cases projection with
      | member name index => exact .memberTail (ih trace)
      | index key =>
          cases trace with
          | head failed => exact .indexHead failed
          | tail head tail => exact .indexTail head (ih tail)

theorem Snapshot.resolves {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {place : PlaceResolution} {values : List Dynamic.Value} {target : ResolvedPlace}
    (snapshot : Snapshot environment before after place values target)
    (trace : ExpressionsEvaluate program context evidence source environment before (keys place.projections) values after) :
    SourcePlaceResolves program context evidence source environment before place target after := by
  cases snapshot with
  | intro lookup initialRead ordered currentRead initialValue selection =>
      exact .intro lookup initialRead (ordered.evaluates trace) currentRead initialValue selection

theorem RootFault.source {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {heap : Heap} {place : PlaceResolution} {reason : SemanticFault}
    (failed : RootFault environment heap place reason) :
    SourcePlaceFaults program context evidence source environment heap place reason heap := by
  cases failed with
  | unbound missing => exact .unbound missing
  | dangling lookup missing => exact .dangling lookup missing

theorem RootReady.key_fault {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {place : PlaceResolution} {reason : SemanticFault}
    (ready : RootReady environment before place)
    (failed : ExpressionsFault program context evidence source environment before (keys place.projections) reason after) :
    SourcePlaceFaults program context evidence source environment before place reason after := by
  cases ready with
  | intro lookup read => exact .projectionExpression lookup read (keys_fault failed)

theorem GetterFault.source {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {place : PlaceResolution} {values : List Dynamic.Value} {reason : SemanticFault}
    (failed : GetterFault environment before after place values reason)
    (trace : ExpressionsEvaluate program context evidence source environment before (keys place.projections) values after) :
    SourcePlaceFaults program context evidence source environment before place reason after := by
  cases failed with
  | dangling lookup read ordered missing =>
      exact .danglingAfterProjections lookup read (ordered.evaluates trace) missing
  | projection lookup initialRead ordered currentRead initialValue fault =>
      exact .projectionRead lookup initialRead (ordered.evaluates trace) currentRead initialValue fault
  | uninitialized lookup initialRead ordered currentRead empty notMapping nonempty =>
      exact .uninitialized lookup initialRead (ordered.evaluates trace) currentRead empty notMapping nonempty

theorem WriteFault.source {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before targetHeap rhsHeap : Heap} {place : PlaceResolution} {target : ResolvedPlace}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {right : Dynamic.Value} {reason : SemanticFault}
    (failed : WriteFault operator target right rhsHeap reason)
    (resolved : SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (evaluated : ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap) :
    SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap := by
  cases failed with
  | operands read root initial path invalid => exact .operands resolved evaluated read root initial path invalid
  | structural read root initial fault => exact .structuralUpdate resolved evaluated read root initial fault

end Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
