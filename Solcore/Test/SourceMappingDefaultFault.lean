import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.SourceSemantics.CoreLowering.CompatiblePathFaults
import Solcore.Frontend.SourceRuntimeValues

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.updateResolvedValue
#check_failure Solcore.Frontend.SourceTypedRuntime.writeResolvedPlace

/-! An absent mapping entry whose value type has no default is a source fault.
Independent source faults determine the actual Core selector/updater token.
Their administrative allocations preserve the initial store prefix, and failure
suppresses replacement and commit continuations. -/

set_option autoImplicit false

namespace Solcore.Test.SourceMappingDefaultFault

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def functionType : Ty := .function .word .word

/-- Non-defaultable mapping values remain admitted source types. -/
example (context : SourceSemantics.Context) :
    TypeWellScoped context [] (.mapping .word functionType) :=
  .mapping (.builtin .word) (.function (.builtin .word) (.builtin .word))

/-- Both successful evaluation prefixes contribute their heap effects before
missing-default failure; no result or failure of either child is invented. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before middle after : Heap)
    (id base index : ExpressionId) (node : ExpressionNode) (key : Core.Word)
    (contains : ContainsExpression source id node)
    (form_eq : node.form = .index base index)
    (layout : OrdinaryRequirementLayout node.requirements node.coercions [])
    (base_evaluates : ExpressionEvaluates program context evidence source
      environment before base (.mapping .word functionType []) middle)
    (index_evaluates : ExpressionEvaluates program context evidence source
      environment middle index (.word key) after) :
    ExpressionEvaluatesOutcome program context evidence source environment
      before id (.fault (.missingMappingDefault functionType)) after := by
  apply ExpressionEvaluatesOutcome.fault
  apply ExpressionFaults.form contains
  rw [form_eq]
  exact .indexDefaultUnavailable layout base_evaluates index_evaluates
    (.word key) .nil (by intro defaultable; cases defaultable)

/-- No function is synthesized to fill an absent entry. -/
example (value : Value) : ¬ DefaultValue functionType value :=
  DefaultValue.not_function .word .word value

/-- The runtime's existing default calculation reports the same absence. -/
example : SourceTypedRuntime.defaultValue? (functionType.size + 1) functionType =
    none := by
  rfl

/-- Missing-default failure propagates through a successfully defaulted mapping
prefix; the outer mapping itself has a default even though its leaf does not. -/
example (outerKey innerKey : Core.Word) :
    ProjectionsFaults
      (some (.mapping .word (.mapping .word functionType) []))
      [.index (.word outerKey), .index (.word innerKey)]
      (.missingMappingDefault functionType) :=
  .indexDefault (.word outerKey) .nil (.mapping .word functionType)
    (.indexDefaultUnavailable (.word innerKey) .nil
      (by intro defaultable; cases defaultable))

/-- Real entries and constructor members also form successful prefixes. -/
example (instantiation : DataConstructorInstantiation) (key : Core.Word) :
    ProjectionsFaults
      (some (.constructed instantiation [.mapping .word functionType []]))
      [.member "table" 0, .index (.word key)]
      (.missingMappingDefault functionType) :=
  .member .head (.indexDefaultUnavailable (.word key) .nil
    (by intro defaultable; cases defaultable))

example (outerKey innerKey : Core.Word) :
    ProjectionsFaults
      (some (.mapping .word (.mapping .word functionType)
        [(.word outerKey, .mapping .word functionType [])]))
      [.index (.word outerKey), .index (.word innerKey)]
      (.missingMappingDefault functionType) :=
  .indexFound (.word outerKey) (.head (.refl (.word outerKey)))
    (.indexDefaultUnavailable (.word innerKey) .nil
      (by intro defaultable; cases defaultable))

/-- Every index expression has run before the pure read faults, and its effects
are preserved in the returned post-index heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before after : Heap)
    (place : PlaceResolution) (location : Location) (initialCell : Cell)
    (key : Core.Word)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initial_read : Heap.Reads before location initialCell)
    (evaluate : SourceProjectionsEvaluate program context evidence source
      environment before place.projections [.index (.word key)] after)
    (current_read : Heap.Reads after location
      { type := .mapping .word functionType,
        value := some (.mapping .word functionType []) }) :
    SourcePlaceFaults program context evidence source environment before place
      (.missingMappingDefault functionType) after :=
  .projectionRead lookup initial_read evaluate current_read .initialized
    (.indexDefaultUnavailable (.word key) .nil
      (by intro defaultable; cases defaultable))

/-- Resolution may have found an existing entry, while the RHS later clears
that mapping. Even plain replacement must traverse the latest root, so it
faults at the missing non-defaultable entry and retains the entire RHS heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before targetHeap rhsHeap : Heap)
    (place : PlaceResolution) (target : ResolvedPlace) (rhs : ExpressionId)
    (right : Value) (key : Core.Word)
    (resolve : SourcePlaceResolves program context evidence source environment
      before place target targetHeap)
    (evaluate : ExpressionEvaluates program context evidence source environment
      targetHeap rhs right rhsHeap)
    (projections : target.projections = [.index (.word key)])
    (root_type : target.rootType = .mapping .word functionType)
    (current_read : Heap.Reads rhsHeap target.location
      { type := .mapping .word functionType,
        value := some (.mapping .word functionType []) }) :
    SourcePlaceAssignmentFaults program context evidence source environment before
      place .equal rhs (.missingMappingDefault functionType) rhsHeap := by
  apply SourcePlaceAssignmentFaults.structuralUpdate resolve evaluate
    current_read root_type.symm .initialized
  rw [projections]
  exact .indexDefaultUnavailable (.word key) .nil
    (by intro defaultable; cases defaultable)

/-- Invalid compound operands do not take precedence over a missing-default
failure while traversing the latest root. The readable-path premise needed
by the operand-fault rule is also impossible for this same root and path. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before targetHeap rhsHeap : Heap)
    (place : PlaceResolution) (target : ResolvedPlace) (rhs : ExpressionId)
    (right : Core.Word) (currentCell : Cell) (initial : Option Value)
    (reason : SemanticFault)
    (resolve : SourcePlaceResolves program context evidence source environment
      before place target targetHeap)
    (evaluate : ExpressionEvaluates program context evidence source environment
      targetHeap rhs (.word right) rhsHeap)
    (selected : target.selected = some (.bool false))
    (current_read : Heap.Reads rhsHeap target.location currentCell)
    (root_type : currentCell.type = target.rootType)
    (root_value : RootInitialValue currentCell initial)
    (fault : ProjectionsFaults initial target.projections reason) :
    AssignmentOperandsInvalid .add target.selected (.word right) ∧
      SourcePlaceAssignmentFaults program context evidence source environment before
        place .add rhs reason rhsHeap ∧
      ¬ ∃ currentSelected, ProjectionsRead initial target.projections currentSelected := by
  refine ⟨?_, .structuralUpdate resolve evaluate current_read root_type root_value fault,
    ?_⟩
  · rw [selected]
    exact .compound .add (.numeric .add (by simp [NumericPair]))
  · rintro ⟨_, read⟩
    exact fault.excludes_read read

/-- The pure fault excludes both a successful read and every leaf modifier's
successful update, without assuming a global evaluation determinism theorem. -/
example (current : Option Value) (projections : List EvaluatedProjection)
    (reason : SemanticFault) (fault : ProjectionsFaults current projections reason)
    (modify : Option Value → Value → Prop) (selected : Option Value) (updated : Value) :
    ¬ ProjectionsRead current projections selected ∧
      ¬ ProjectionsUpdate modify current projections updated :=
  ⟨fault.excludes_read, fault.excludes_update⟩

/-- Without an RHS, bit-not's structural write cannot acquire a missing-default
failure after target resolution in the same post-index heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before after : Heap)
    (place : PlaceResolution) (target : ResolvedPlace)
    (resolved : SourcePlaceResolves program context evidence source environment
      before place target after)
    (currentCell : Cell) (initial : Option Value) (reason : SemanticFault)
    (current_read : Heap.Reads after target.location currentCell)
    (initial_value : RootInitialValue currentCell initial) :
    ¬ ProjectionsFaults initial target.projections reason :=
  resolved.excludes_projection_fault current_read initial_value

namespace CoreBridge
open Core SourceSemantics.CoreLowering SourceCoreCompatibleDataPlaces
open CompatiblePayload CompatibleMixedRoute CompatibleMapping.MixedPaths

/-- An independently derived missing default, including a defaulted or member
prefix, constructs the actual Core getter and updater failures. The updater's
replacement and commit continuation can be any expressions: neither is evaluated.
The old snapshot does not participate in this traversal of the current root. -/
theorem current_root_missing_default
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {sourceProjections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Core.Ty)}
    {path : PreparedPath checked source site root sourceProjections position steps keySites leaf}
    {prepared : Prepared} {keys : List Core.Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {current : Dynamic.Value} {value : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (fault : Dynamic.ProjectionsFaults (some current) projections (.missingMappingDefault functionType))
    {identities : Dynamic.Value → Core.Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Core.Environment) (store : Core.Store) (currentExpression keyExpression replacement next : Core.Expr)
    (selected : DataEquality.Selects environment currentExpression value)
    (keysSelected : DataEquality.Selects environment keyExpression (DataPatternValues.packValues keys))
    (output : Core.Ty) :
    ∃ token count finalStore administrative,
      FaultToken checked registry current steps projections (.missingMappingDefault functionType) token count ∧
      Core.Evaluates environment store (select prepared steps currentExpression keyExpression)
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Core.Evaluates environment store
        (Core.LanguageResult.bind output (update prepared steps type currentExpression keyExpression replacement) next)
        (.inLeft output (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree represented fault prepared
  obtain ⟨finalStore, administrative, _, read, updated, appended, counted⟩ :=
    tree.preserves faithful observations keyLength environment store currentExpression keyExpression replacement selected keysSelected
  exact ⟨token, count, finalStore, administrative, receipt, read,
    Core.LanguageResult.bind_failure output updated, appended, counted⟩

end CoreBridge

end Solcore.Test.SourceMappingDefaultFault
