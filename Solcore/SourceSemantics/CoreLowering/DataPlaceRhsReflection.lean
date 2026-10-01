import Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection

/-! The actual three-slot RHS continuation reflects through the universal child
expression theorem. It either constructs the source RHS fault with its effects,
or retains the RHS value/heap and the actual four-slot modifier continuation.
Prefix/RHS executions are semantic output witnesses, never static assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

/-- The literal subtree of execute after binding its RHS value. -/
def remainder (prepared : Prepared) (keyType : Ty) (next : Expr) (outputType : Ty)
    (operator : Option BinaryOp) (invalid : Word) : Expr :=
  LanguageResult.bind outputType
    (modified prepared.route.leafType operator false (.var 1) (.var 0) invalid)
    (LanguageResult.bind outputType
      (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next)))

theorem prefix_remainder_eq (prepared : Prepared) (keyType : Ty) (rhs next : Expr)
    (outputType : Ty) (operator : Option BinaryOp) (invalid : Word) :
    DataPlacePrefixReflection.remainder prepared keyType rhs next outputType operator false invalid =
      LanguageResult.bind outputType (shift 3 rhs) (remainder prepared keyType next outputType operator invalid) := rfl

/-- Actual RHS output, including independent source meaning and all heap,
world and admin-frame extensions relative to the already reflected snapshot. -/
structure Execution (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (target : Dynamic.ResolvedPlace) (coreEnvironment : Environment)
    (initialStore : Store) (initialMap : LocationMap) (initialWorld : StoreTyping) (before targetHeap : Dynamic.Heap)
    (resolution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  right : Dynamic.Value
  value : Value
  heap : Dynamic.Heap
  store : Store
  mapping : LocationMap
  world : StoreTyping
  sourceTrace : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap id right heap
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
    resolution.snapshot coreEnvironment) resolution.store (shift 3 lowered.expression) (.inRight .word value) store
  related : ValueRep checked.catalog signatures functions mapping world place.type right value prepared.route.leafType
  heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store
  maps : LocationMap.Extends resolution.mapping mapping
  worlds : WorldExtends resolution.world world
  frame : AdministrativePreserved resolution.mapping resolution.store mapping store
  metadata : Dynamic.HeapMetadataExtend targetHeap heap

inductive Result (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) (next : Expr) (outputType : Ty)
    (operator : Syntax.ValueAssignOp) (invalid : Word) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs lowered next outputType operator invalid result finalStore
  | ready {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
      (resolution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
        coreEnvironment store mapping world before targetHeap)
      (right : Execution checked signatures functions program context evidence source environment prepared codes sourceTypes place target
        coreEnvironment store mapping world before targetHeap resolution rhs lowered)
      (continuation : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        resolution.snapshot right.value coreEnvironment) right.store
        (remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs lowered next outputType operator invalid result finalStore

/-- Consume the output of whole-resolution reflection. Its RHS execution is
extracted from the actual remainder and reflected under exactly three hidden
slots. No child source trace, evaluation or exact-value weakening is assumed. -/
theorem reflects {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {administrativeContext : Core.Context}
    (meaning : Reflects (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (sourceType : node.type = place.type) (coreType : lowered.type = prepared.route.leafType)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {next : Expr} {outputType : Ty} {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value}
    (resolution : DataPlacePrefixReflection.Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
      environment coreEnvironment before store mapping world lowered.expression next outputType
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid result finalStore) :
    Result checked signatures functions program context evidence source faults prepared codes sourceTypes place environment
      coreEnvironment before store mapping world id lowered next outputType operator invalid result finalStore := by
  cases resolution with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remaining =>
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro i value found; exact found
    have reflectRhs := fun {right : Value} {rhsStore : Store}
        (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          resolution.snapshot coreEnvironment) resolution.store (shift 3 lowered.expression) right rhsStore) =>
      DataPlaceChildExpressions.reflects meaning generated found (environments.extend resolution.maps resolution.worlds)
        resolution.heaps (locals.mono resolution.metadata) sameEnvironment
        [resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]
        (by simpa only [Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
          snapshotEnvironment, keysEnvironment, referenceEnvironment] using evaluated)
    cases remaining with
    | caseLeft rhsEvaluated failed =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, sourceRhs, represented, rhsHeaps, maps, worlds, frame, metadata⟩ :=
        reflectRhs rhsEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceRhs with
        | fault sourceRhs =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.rhs sourceTrace sourceRhs) rfl tokenRep rhsHeaps (resolution.maps.trans maps)
                (resolution.worlds.trans worlds) (resolution.frame.trans frame) (resolution.metadata.trans metadata)
    | caseRight rhsEvaluated remaining =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, sourceRhs, represented, rhsHeaps, maps, worlds, frame, metadata⟩ :=
        reflectRhs rhsEvaluated
      cases represented with
      | value payload =>
        cases sourceRhs with
        | value sourceRhs =>
          exact .ready sourceTrace resolution
            { right := _
              value := _
              heap := rhsHeap
              store := _
              mapping := rhsMap
              world := rhsWorld
              sourceTrace := sourceRhs
              evaluated := rhsEvaluated
              related := by simpa only [payloadModel, sourceType, coreType] using payload
              heaps := rhsHeaps
              maps := maps
              worlds := worlds
              frame := frame
              metadata := metadata }
            remaining

end Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
