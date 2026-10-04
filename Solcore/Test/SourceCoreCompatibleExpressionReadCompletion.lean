import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning

/-! Consumers of shared original-completion inversion. The actual compiler and
independent source typing supply a receipt; native typing alone never supplies
a source declaration or a generalized-cell history. No runner is added. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleExpressionReadCompletion
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

section Actual
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode}
  (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
  (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
  (unique : NodeOccurrencesUnique source)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (typed : ExpressionHasType source context id node.type)
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

include accepted read unique declarations typed extension in
/-- All actual ordinary reads use the unchanged public reflection interface. -/
theorem actual_completed (uninitialized : ∀ expression location, faults (.uninitializedLocation location) (reasonAt expression)) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (fun current occurrence code => current = scope ∧ occurrence = id ∧ code = lowered) faults := by
  intro current occurrence code receipt
  obtain ⟨rfl, rfl, rfl⟩ := receipt
  exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized
    (CompatibleExpressionReads.loweredRead_of_accepted accepted read unique declarations typed)

include accepted read unique declarations typed extension in
/-- The mapping branch returns the independent raw source rule. Ordinary and
staged consumers can wrap this same result without rerunning native code. -/
theorem actual_mapping_form {name : String} {binder : Resolved.LocalId} {declared : TypedBinder}
    {key value : TypeSystem.Ty}
    (form : node.form = .reference name (.local binder))
    (declaration : SourceCoreDataPlaces.rootBinder source binder = .ok declared)
    (declaredType : declared.scheme.body = .mapping key value)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    {result : Value} {finalStore : Store}
    (completed : Evaluates actual store (lowered.expression.rename ξ) result finalStore) :
    ∃ sourceValue after,
      Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form [] [] sourceValue after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping world node.type lowered.type faults (.value sourceValue) result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨certificate, sameType, binding, mappingType⟩ :=
    RecursiveStageMappingReadMeaning.of_accepted accepted read unique declarations typed form declaration declaredType
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans (CompatibleExpressionReads.metadata_of_read read).found)
  obtain ⟨sourceValue, after, raw, represented, rest⟩ :=
    certificate.mapping_completed (faults := faults) functions extension program context evidence binding mappingType
      environments heaps locals agrees completed
  exact ⟨sourceValue, after, by simpa only [nodeEq] using raw,
    by simpa only [nodeEq, sameType] using represented, rest⟩
end Actual

section Native
/-- A present ordinary optional cell keeps the complete original store. -/
theorem ordinary_present {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {reason : Word} {present result : Value}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inRight .unit present))
    (completed : Evaluates environment before (OptionalCell.read type (.var index) reason) result after) :
    result = .inRight .word present ∧ after = before := by
  rcases CompatibleExpressionReadCompletion.ordinary_completed lookup read completed with
    ⟨_, _, same, resultEq, storeEq⟩ | ⟨_, _, impossible, _⟩
  · cases same; exact ⟨resultEq, storeEq⟩
  · cases impossible

/-- An absent ordinary nonmapping cell returns its real fault carrier and
preserves the original store. Its source attribution is supplied separately. -/
theorem ordinary_absent {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {reason : Word} {result : Value}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit))
    (completed : Evaluates environment before (OptionalCell.read type (.var index) reason) result after) :
    result = .inLeft type (.word reason) ∧ after = before := by
  rcases CompatibleExpressionReadCompletion.ordinary_completed lookup read completed with
    ⟨_, _, impossible, _⟩ | ⟨_, _, _, resultEq, storeEq⟩
  · cases impossible
  · exact ⟨resultEq, storeEq⟩

/-- Lazy mapping initialization exposes the exact original write and retains
all other native cells, including arbitrary unused administrative payloads. -/
theorem mapping_write_other {environment : Environment} {before after : Store}
    {index target other : Nat} {type : Ty} {empty result : Value} {literal : Expr}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : before.read? target = some (.inLeft type .unit)) (quoted : Quoted empty literal)
    (completed : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after)
    (different : other ≠ target) :
    result = .inRight .word empty ∧ before.write? target (.inRight .unit empty) = some after ∧
      after.read? other = before.read? other := by
  rcases RecursiveStageMappingReadMeaning.read_completed lookup read quoted completed with
    ⟨_, _, impossible, _⟩ | ⟨_, _, same, resultEq, written⟩
  · cases impossible
  · cases same
    exact ⟨resultEq, written, Store.write?_preserves_other written different⟩
end Native

/-- Generalized-cell history is outside ordinary optional-cell representation. -/
theorem generalized_excluded {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : Core.DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (represented : GenericHeap.CellRepresents model mapping world cell value type)
    (generalized : cell.generalized ≠ none) : False := generalized represented.ordinary

end Tests.SourceCoreCompatibleExpressionReadCompletion
