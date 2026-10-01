import Solcore.SourceSemantics.CoreLowering.CompatiblePlacePrefixReflection

/-! Reflect the real three-slot RHS continuation after target resolution.
The source RHS outcome, latest heap and four-slot modifier continuation are
outputs obtained from the universal expression induction hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

def remainder (prepared : Prepared) (keyType : Ty) (next : Expr) (outputType : Ty)
    (operator : Option BinaryOp) (invalid : Word) : Expr :=
  LanguageResult.bind outputType
    (modified prepared.route.leafType operator false (.var 1) (.var 0) invalid)
    (LanguageResult.bind outputType
      (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next)))

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (environment : Dynamic.Environment) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (sourceTypes : List TypeSystem.Ty) (place : PlaceResolution) (leaf : TypeSystem.Ty)
    (target : Dynamic.ResolvedPlace) (coreEnvironment : Environment)
    (initialStore : Store) (initialMap : LocationMap) (initialWorld : StoreTyping) (before targetHeap : Dynamic.Heap)
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) where
  right : Dynamic.Value
  value : Value
  heap : Dynamic.Heap
  store : Store
  mapping : LocationMap
  world : StoreTyping
  meaning : CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
    (faults := faults) resolution id node lowered environment (.value right) heap (.inRight .word value) store mapping world
  related : ValueRep checked registry functions mapping world leaf right value prepared.route.leafType

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) (next : Expr) (outputType : Ty)
    (operator : Syntax.ValueAssignOp) (invalid : Word) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore
  | ready {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
      (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap)
      (right : Execution checked registry functions program context evidence source faults environment prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before targetHeap resolution rhs node lowered)
      (continuation : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) right.value coreEnvironment) right.store
        (remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs node lowered next outputType operator invalid result finalStore

/-- Source and Core RHS types are connected by the retained raw runtime view,
not by inverting the many-to-one native type projection. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (meaning : Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (coreType : lowered.type = prepared.route.leafType)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {next : Expr} {outputType : Ty} {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value}
    (resolution : CompatiblePlacePrefixReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes
      place leaf environment coreEnvironment before store mapping world lowered.expression next outputType
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid result finalStore) :
    Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
      coreEnvironment before store mapping world id node lowered next outputType operator invalid result finalStore := by
  cases resolution with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remaining =>
    cases remaining with
    | caseLeft rhsEvaluated failed =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        CompatiblePlaceRhs.reflects resolution meaning generated found environments locals rhsEvaluated
      cases represented : rhsResult.represented with
      | fault tokenRep =>
        cases rhsResult.trace with
        | fault sourceRhs =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.rhs sourceTrace sourceRhs) rfl tokenRep rhsResult.heaps
                (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)
                (resolution.frame.trans rhsResult.frame) (resolution.metadata.trans rhsResult.metadata)
    | caseRight rhsEvaluated remaining =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        CompatiblePlaceRhs.reflects resolution meaning generated found environments locals rhsEvaluated
      cases represented : rhsResult.represented with
      | value payload =>
        exact .ready sourceTrace resolution
          { right := _
            value := _
            heap := rhsHeap
            store := _
            mapping := rhsMap
            world := rhsWorld
            meaning := rhsResult
            related := .compatible rhsView (by simpa only [payloadModel, coreType] using payload) } remaining

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection
