import Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget

/-! Reflection of execute's real reference/key/getter prefix. The universal
child theorem reconstructs each index trace in source order, before the live
root is read. Success exposes the real three-slot RHS continuation; failures
return the source fault and skip every later phase. These executions are output
witnesses, not fields of a static compiler certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

/-- The literal remaining subtree of `execute`, after its snapshot binder. -/
def remainder (prepared : Prepared) (keyType : Ty) (rhs next : Expr) (outputType : Ty)
    (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word) : Expr :=
  LanguageResult.bind outputType (shift 3 rhs)
    (LanguageResult.bind outputType
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalid)
      (LanguageResult.bind outputType
        (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
        (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next))))

theorem execute_eq (prepared : Prepared) (reference : Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word) :
    execute prepared reference keys rhs next outputType operator bitNot invalid =
      .letE reference (LanguageResult.bind outputType (shift 1 keys.expression)
        (LanguageResult.bind outputType (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
          (remainder prepared keys.type rhs next outputType operator bitNot invalid))) := rfl

private theorem missing_token {faults : FaultRep} {missing : TypeSystem.Ty → Word}
    (tokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {initial : Option Dynamic.Value} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ProjectionsFaults initial projections reason) : faults reason (DataPlaceExactFault.token missing reason) := by
  induction fault with
  | indexDefaultUnavailable => exact tokens _
  | indexFound _ _ _ ih | indexDefault _ _ _ _ ih | member _ _ ih => exact ih

/-- A semantic prefix result. The success case retains every actual value and
store needed by RHS/modifier/setter reflection, including the source snapshot.
The failure case retains the final child/getter heap and diagnostic relation. -/
inductive Result (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore
  | resolved {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target after)
      (execution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
        coreEnvironment store mapping world before after)
      (continuation : Evaluates (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        execution.snapshot coreEnvironment) execution.store
        (remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore

/-- Every actual completed assignment first either produces a source target
fault or resolves a source target before entering its RHS. No source index
trace or child/helper execution is supplied by the caller. -/
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
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {sourceLocation : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (initialRead : Dynamic.Heap.Reads before sourceLocation initialCell)
    (rootType : initialCell.type = prepared.route.rootSourceType)
    (invalidToken : faults (.uninitializedLocation sourceLocation) prepared.invalidProjection)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalid)
      result finalStore) :
    Result checked signatures functions program context evidence source faults prepared codes sourceTypes place environment
      coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i value found; exact found
  have reflectKeys := fun {keyValue : Value} {keyStore : Store}
      (evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) keyValue keyStore) =>
    DataPlaceKeyOrder.reflects layout.keys meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees sameEnvironment
        [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment] using evaluated)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated (Evaluates.var coreLookup)
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflectKeys keysEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceTrace with
        | fault sourceTrace =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.projectionExpression lookup initialRead sourceTrace) rfl tokenRep finalHeaps maps worlds frame metadata
    | caseRight keysEvaluated tail =>
      obtain ⟨outcome, keyHeap, keyMap, keyWorld, sourceTrace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
        reflectKeys keysEvaluated
      cases represented with
      | @values sources values keysRelated =>
        cases sourceTrace with
        | @values _ evaluated _ shaped sourceTrace =>
          obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata sourceLocation initialCell initialRead
          have currentReference := reference.extend keyMaps keyWorlds
          have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
              (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
              ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
                (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) checked.catalog.definitions :=
            .cons (DataPlaceResolvedTarget.values_typed keysRelated)
              (.cons (.cellRef currentReference.typed) ((environments.extend keyMaps keyWorlds).runtime_hasTypes))
          have currentRaw : DataPlaceRouteCertificates.RawPath checked signatures source currentCell.type prepared.route.rootType
              steps place.projections place.type prepared.route.leafType sourceTypes := by
            rw [currentType, rootType]; exact raw
          have currentLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared currentCell.type := by
            rw [currentType, rootType]; exact layout.root
          have keyLength : prepared.keyTypes.length = values.length := layout.keyTypes ▸ keysRelated.length.2
          have reflectGetter := fun {snapshotValue : Value} {snapshotStore : Store}
              (evaluated : Evaluates (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment) _
                (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
                snapshotValue snapshotStore) =>
            DataPlaceGetterReflection.reflects_at functionTypes layouts observations faithful currentRaw preparation
              shaped keysRelated keyLength currentLayout keyHeaps currentReference currentRead typedEnvironment layout.getterTyped
              (.var rfl) (.var rfl) evaluated
          cases tail with
          | caseLeft getterEvaluated failed =>
            obtain ⟨futureWorld, administrative, resultRep, extension, finalHeaps, _, frame, _⟩ := reflectGetter getterEvaluated
            cases resultRep with
            | missing root fault =>
              cases failed with
              | inLeft valueEvaluated =>
                cases valueEvaluated with
                | var found =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                  subst_vars
                  exact .fault (.projectionRead lookup initialRead sourceTrace currentRead root fault) rfl
                    (missing_token missingTokens fault) finalHeaps keyMaps (keyWorlds.trans extension) (keyFrame.trans frame) metadata
            | uninitialized root nonempty =>
              cases root with
              | uninitialized notMapping =>
                cases failed with
                | inLeft valueEvaluated =>
                  cases valueEvaluated with
                  | var found =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                    subst_vars
                    exact .fault (.uninitialized lookup initialRead sourceTrace currentRead rfl notMapping nonempty) rfl
                      invalidToken finalHeaps keyMaps (keyWorlds.trans extension) (keyFrame.trans frame) metadata
          | caseRight getterEvaluated remaining =>
            obtain ⟨futureWorld, administrative, resultRep, extension, finalHeaps, _, frame, _⟩ := reflectGetter getterEvaluated
            cases resultRep with
            | @read initial selected snapshot root read snapshotRelated =>
              exact .resolved (.intro lookup initialRead sourceTrace currentRead root read)
                { target := target
                  sources := sources
                  values := values
                  snapshot := _
                  keyStore := _
                  store := _
                  mapping := keyMap
                  world := futureWorld
                  reference := currentReference.extend (.refl _) extension
                  shaped := shaped
                  keysEvaluated := keysEvaluated
                  snapshotEvaluated := getterEvaluated
                  keysRelated := keysRelated.extend (.refl _) extension
                  snapshotRelated := snapshotRelated
                  heaps := finalHeaps
                  maps := keyMaps
                  worlds := keyWorlds.trans extension
                  frame := keyFrame.trans frame
                  metadata := metadata }
                remaining

end Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection
