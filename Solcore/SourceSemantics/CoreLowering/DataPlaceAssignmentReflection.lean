import Solcore.SourceSemantics.CoreLowering.DataPlaceTailReflection

/-! Whole execute reflection from static compilation receipts and a universal
child-expression theorem. Key/RHS/getter/modifier/setter evaluations and source
traces are all extracted or constructed here, never certificate assumptions.
The remaining statement continuation is exposed under its real seven slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces

theorem reflects {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    {steps : List Step} {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (raw : DataPlaceRouteCertificates.RawPath checked signatures source prepared.route.rootSourceType prepared.route.rootType
      steps place.projections place.type prepared.route.leafType sourceTypes)
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    (meaning : Reflects (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : DataEquality.IdentityFaithful identities)
    (missingTokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsSourceType : node.type = place.type) (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp} {invalid : Word}
    (operatorProfile : operator = .equal ∨ place.type = .word ∨ place.type = .integer)
    (invalidOperandToken : faults (.invalidAssignmentOperands operator) invalid)
    (setterTyped : HasType
      (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {sourceLocation : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (initialRead : Dynamic.Heap.Reads before sourceLocation initialCell)
    (rootType : initialCell.type = prepared.route.rootSourceType)
    (invalidProjectionToken : faults (.uninitializedLocation sourceLocation) prepared.invalidProjection)
    {next : Expr} {outputType : Ty} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid) result finalStore) :
    DataPlaceTailReflection.Result checked signatures functions program context evidence source faults place operator rhs
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  have resolution := DataPlacePrefixReflection.reflects layout raw preparation meaning functionTypes layouts observations faithful
    missingTokens environments heaps locals slot lookup initialRead rootType invalidProjectionToken completed
  have rhs := DataPlaceRhsReflection.reflects meaning rhsGenerated found rhsSourceType rhsCoreType environments locals resolution
  cases rhs with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault sourceFault resultEq tokenRep heaps maps worlds frame metadata
  | ready sourceTrace resolution right continuation =>
    have targetType := (DataPlaceSourceOrder.resolve_root_type sourceTrace resolution.metadata lookup initialRead).trans rootType
    exact DataPlaceTailReflection.reflects_ready functionTypes layouts observations faithful raw preparation layout.root layout.keyTypes
      missingTokens operatorProfile invalidOperandToken setterTyped environments sourceTrace targetType resolution right continuation

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentReflection
