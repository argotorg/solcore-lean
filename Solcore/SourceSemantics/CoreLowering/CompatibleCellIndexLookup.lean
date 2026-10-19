import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexLookup
import Solcore.SourceSemantics.CoreLowering.CellMappingHeap

/-! The actual general-key comparator retains mixed ordinary and generalized
cells. Only its native administrative suffix is appended. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellIndex
open Core Frontend CompatiblePayload CompatibleMapping CompatibleEquality DataEquality
open GeneralHeap ReadOnly CompatibleExpressionPrimitives
open CompatibleGeneralIndex

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {cells : GenericHeap.CellModel ambient.definitions}

private theorem closed_hasType {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) : HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

/-- Comparator closure allocations preserve the source heap and every existing
administrative cell. The captured actual slots must all be typed. -/
theorem lookup_preserves_heap (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {layout : Core.OrderedMapping.Layout} (keyType : layout.keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (missingBase : Word) :
    ∃ result finalStore futureWorld suffix,
      ReadResult checked registry functions mapping futureWorld sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates (key :: Transport.carrier header fallback layout entries :: environment) store
        (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0)) result finalStore ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      finalStore = store ++ suffix := by
  obtain ⟨result, meaning, evaluated⟩ := lookup_meaning prepared faithful functionLeaves keyType fields keyRep
    (key :: Transport.carrier header fallback layout entries :: environment) store missingBase (.var 1) (.var 0) (.var rfl) (.var rfl)
  have nativeTyped := fields.represents.runtime_hasType
  have actualTyped := RuntimeEnvironmentHasTypes.cons keyRep.runtime_hasType (.cons nativeTyped environmentTyped)
  have helperTyped : HasType (layout.keyType :: SourceCoreMappingWithDefault.type layout :: context)
      (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0))
      (LanguageResult.resultType layout.valueType) ambient.definitions := by
    apply SourceCoreMappingWithDefault.lookup_hasType missingBase (fields.registered.extend_definitions ambient.basePrefix)
    · simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType, SourceCoreDataEquality.comparatorType, keyType] using closed_hasType (prepared.typed.extend_definitions ambient.basePrefix) _
    · exact .var rfl
    · exact .var rfl
  obtain ⟨suffix, appended, _⟩ := Transport.lookupStore_extension prepared layout
    (key :: Transport.carrier header fallback layout entries :: environment) store header fallback entries key
  obtain ⟨futureWorld, extension, futureHeaps, resultTyped, unchanged⟩ :=
    CellMappingHeap.evaluation_preserves_frame heaps actualTyped helperTyped evaluated appended
  exact ⟨result, _, futureWorld, suffix, CompatibleExpressionIndices.extend_read_result meaning extension, evaluated, futureHeaps, extension, unchanged, appended⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellIndex
