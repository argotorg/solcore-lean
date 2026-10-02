import Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentRhs

/-! Forward finite meaning of bare assignments. These laws preserve the exact
independent source trace, including a fault after RHS effects. The returned
continuation runs in its real renamed seven-slot environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {certificate : Certificate} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}
  {entry : ProtectedExpressionMeaning.Entry}

private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left) (second : Dynamic.Heap.Writes heap location value right) : left = right := by
  have cells : ∀ {before first second : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell},
      Dynamic.Heap.CellsWrite before index value first → Dynamic.Heap.CellsWrite before index value second → first = second := by
    intro before first second index value left
    induction left generalizing second with
    | head => intro right; cases right; rfl
    | tail _ ih => intro right; cases right with | tail rest => exact congrArg (List.cons _) (ih rest)
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

theorem preserves_prefix_bounded (budget : Nat)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (bounded : size ≤ budget) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  cases trace with
  | intro resolved evaluated written =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolved.sound
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ :=
      ProtectedBareAssignment.rhs_preserves_at snapshot _
        (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) generated found environments heaps locals agrees actualTyped installed (.value evaluated)
    cases related : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      have saved := snapshot.represented.extend result.maps result.worlds
      cases written with
      | intro read sameType initial update written =>
        cases update with
        | leaf applied =>
          rcases modifier_total observations profile saved rightRep
            (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
            ⟨invalidOperands, _⟩ | ⟨replacement, updatedValue, replacementRep, generatedApply, modified⟩
          · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim
          · have same := DataPlaceModifier.assignment_functional generatedApply applied
            subst replacement
            obtain ⟨generatedHeap, finalStore, _, generatedWrite, finalHeaps, frame, metadata, typed, agreement⟩ :=
              commit layout snapshot bare result rightRep replacementRep applied (by simpa only [layout.sameType] using modified) actualTyped
            have same := writes_functional generatedWrite written
            subst generatedHeap
            exact ⟨updatedValue, finalStore, rhsMap, rhsWorld,
              [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
                .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target],
              replacementRep, finalHeaps, result.maps, result.worlds, frame, metadata, rfl, typed, agreement⟩

theorem preserves_prefix
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignment.has_size trace
  exact preserves_prefix_bounded size layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) invalid

private theorem no_target_fault
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
    (bare : place.projections = []) {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after) : False := by
  cases fault with
  | unbound missing => exact missing.excludes_lookup snapshot.lookup
  | dangling lookup missing =>
    have same := lookup.functional snapshot.lookup
    cases same
    exact missing.excludes_read snapshot.read
  | projectionExpression _ _ fault => rw [bare] at fault; cases fault
  | danglingAfterProjections lookup _ evaluated missing =>
    rw [bare] at evaluated
    cases evaluated
    have same := lookup.functional snapshot.lookup
    cases same
    exact missing.excludes_read snapshot.read
  | projectionRead _ _ evaluated _ _ fault =>
    rw [bare] at evaluated
    cases evaluated
    cases fault
  | uninitialized _ _ evaluated _ _ _ nonempty =>
    rw [bare] at evaluated
    cases evaluated
    exact nonempty rfl

/-- All independently specified bare assignment faults retain RHS prefix
state. A target fault or structural traversal fault contradicts the empty
path and live lexical reference, rather than being silently reclassified. -/
theorem preserves_fault_reachable_bounded (budget : Nat)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator id reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have phase := snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  cases trace with
  | target fault => exact (no_target_fault snapshot bare fault.sound).elim
  | rhs resolve fault =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve.sound
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ :=
      ProtectedBareAssignment.rhs_preserves_at snapshot _
        (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) generated found environments heaps locals agrees actualTyped installed (.fault fault)
    cases represented : result.represented with
    | fault token =>
      exact ⟨_, rhsStore, rhsMap, rhsWorld, phase.wrap (LanguageResult.bind_failure outputType result.evaluated), token,
        result.heaps, result.maps, result.worlds, result.frame, result.metadata⟩
  | operands resolve evaluated _ _ _ _ invalidOperands =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve.sound
    obtain ⟨value, rhsStore, rhsMap, rhsWorld, result⟩ :=
      ProtectedBareAssignment.rhs_preserves_at snapshot _
        (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) generated found environments heaps locals agrees actualTyped installed (.value evaluated)
    cases represented : result.represented with
    | @value _ rightValue payload =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType _ rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      rcases modifier_total observations profile (snapshot.represented.extend result.maps result.worlds) rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid with
          ⟨_, failed⟩ | ⟨_, _, _, applied, _⟩
      · have failed : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
            (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
            (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by simpa only [layout.sameType] using failed
        exact ⟨invalid, rhsStore, rhsMap, rhsWorld,
          phase.wrap (LanguageResult.bind_success outputType result.evaluated (LanguageResult.bind_failure outputType failed)),
          invalidToken _ _ invalidOperands, result.heaps, result.maps, result.worlds, result.frame, result.metadata⟩
      · exact (DataPlaceModifier.assignment_excludes_invalid applied invalidOperands).elim
  | structuralUpdate resolve _ _ _ _ fault =>
    obtain ⟨rfl, rfl⟩ := snapshot.resolve_unique bare resolve.sound
    cases fault

theorem preserves_fault_reachable
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignmentFaults.has_size trace
  exact preserves_fault_reachable_bounded size layout bare extension
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) next outputType invalid invalidToken

/-- Compatibility entry point retaining the original operand-token premise. -/
theorem preserves_fault
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact preserves_fault_reachable layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped trace next outputType invalid
    (AssignmentOperandDiagnostics.of_unconditional invalidToken)

end Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
