import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTailReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceSuccess
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareAssignmentContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts

/-! Dynamic projected-assignment receipts retain the original native tail and
independent source measurements. These receipts are semantic outputs, never
static compiler evidence. The seven written values are typed directly from
the reflected setter/write phases. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

inductive KeyResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping) (index : Nat)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceFaults program sourceSize context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore
  | keys {sourceSize remainingSize : Nat} {location : Dynamic.Location} {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (trace : SourceExecutionSize.SourceProjectionsEvaluate program sourceSize context evidence source environment before place.projections resolved after)
      (execution : CompatiblePlaceTargetKeys.Execution checked registry functions prepared place codes sourceTypes location resolved
        coreEnvironment before after store mapping world index)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (keysEnvironment prepared.route.rootType execution.target (packValues execution.values) coreEnvironment)
        execution.keyStore (CompatiblePlaceKeyReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore


inductive PrefixResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceFaults program sourceSize context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      PrefixResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore
  | resolved {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target after)
      (execution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before after)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        (.inRight .unit execution.snapshot) coreEnvironment) execution.store
        (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      PrefixResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore


inductive RhsResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) (next : Expr) (outputType : Ty)
    (operator : Syntax.ValueAssignOp) (invalid : Word) (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      RhsResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore
  | ready {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      (sourceTrace : SourceExecutionSize.SourcePlaceResolves program sourceSize context evidence source environment before place target targetHeap)
      (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap)
      (right : CompatiblePlaceRhsReflection.Execution checked registry functions program context evidence source faults environment prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
      {rhsSize : Nat}
      (rhsTrace : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right.right right.heap)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
        (CompatiblePlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
      RhsResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore


inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (keyType : Ty) (actualContext : Core.Context)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore
  | committed {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleRenamedPlaceSuccess.writtenContext prepared keyType actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore


theorem KeyResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {result : Value} {finalStore : Store}
    (receipt : KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore) :
    CompatiblePlaceKeyReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | keys lookup trace execution _ remaining =>
    exact .keys lookup trace.sound execution remaining.sound

theorem PrefixResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {result : Value} {finalStore : Store}
    (receipt : PrefixResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore) :
    CompatiblePlacePrefixReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | resolved trace execution _ remaining =>
    exact .resolved trace.sound execution remaining.sound

theorem RhsResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {next : Expr} {outputType : Ty}
    {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value} {finalStore : Store}
    (receipt : RhsResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore) :
    CompatiblePlaceRhsReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | ready trace execution right _ _ remaining =>
    exact .ready trace.sound execution right remaining.sound

theorem ResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {keyType : Ty} {actualContext : Core.Context} {place : PlaceResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {environment : Dynamic.Environment} {actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world next output value finalStore) :
    CompatiblePlaceTailReflection.Result checked registry functions program context evidence source faults place operator rhs
      environment actual before store mapping world next output value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace.sound same represented heaps maps worlds frame metadata
  | committed trace heaps maps worlds frame metadata count _ _ remaining =>
    exact .committed trace.sound heaps maps worlds frame metadata count remaining.sound

theorem ResultAt.weaken_bound {size larger : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {keyType : Ty} {actualContext : Core.Context} {place : PlaceResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {environment : Dynamic.Environment} {actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt size checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world next output value finalStore) (bound : size ≤ larger) :
    ResultAt larger checked registry functions program context evidence source faults prepared keyType actualContext place operator rhs
      environment actual before store mapping world next output value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | committed trace heaps maps worlds frame metadata count typed smaller remaining =>
    exact .committed trace heaps maps worlds frame metadata count typed (Nat.lt_of_lt_of_le smaller bound) remaining

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts
