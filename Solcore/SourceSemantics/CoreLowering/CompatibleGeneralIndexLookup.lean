import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexTerminal
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityPayload
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning

/-! General mapping keys use the existing prepared comparator. Full payloads
supply structural equality observations; callable leaves separately authenticate
identities. The actual captured environment remains typed throughout allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend CompatiblePayload CompatibleMapping CompatibleEquality DataEquality
open GeneralHeap ReadOnly CompatibleExpressionPrimitives

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

private theorem observed_entries (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {keyType valueType : Ty} (projected : keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    CoreLowering.OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  subst keyType
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value rest => exact .cons (CompatibleEquality.ValueRep.observation functionLeaves key) value (ih rest)

/-- Finite lookup for every represented key type, using actual prepared code. -/
theorem lookup_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {layout : Core.OrderedMapping.Layout} (keyType : layout.keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (missingBase : Word) (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates environment store (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) result
        (Transport.lookupStore prepared layout environment store header fallback entries key) := by
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry faithful
  have fullCorrect : CoreLowering.OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey layout.keyType) equal := by
    refine ⟨fun left right => correct.equivalent ?_ ?_⟩
    · simpa only [keyType] using CompatibleEquality.ValueRep.observation functionLeaves left
    · simpa only [keyType] using CompatibleEquality.ValueRep.observation functionLeaves right
  have observed : CompatibleMappingComparison.KeyRep prepared registry identities sourceLookup key := by
    simpa only [keyType] using CompatibleEquality.ValueRep.observation functionLeaves keyRep
  have evaluated := Transport.lookup_evaluates prepared layout keyType faithful equal correct observed
    (observed_entries prepared functionLeaves keyType fields.stored) environment store missingBase header fallback
    mappingExpression keyExpression mappingSelected keySelected
  obtain ⟨found, sourceLookup⟩ := lookup_total sourceLookup sources
  cases sourceLookup with
  | found found =>
    obtain ⟨value, located, represented⟩ := lookup_preserves fullCorrect keyRep fields.stored found
    exact ⟨_, .found found represented, by simpa only [located, SourceCoreMappingWithDefault.selectedValue, Option.or] using evaluated⟩
  | absent absent =>
    have missing := CoreLowering.OrderedMapping.absent_related fullCorrect keyRep (entries_related fields.stored) absent
    rw [missing] at evaluated
    cases fields.default with
    | absent noDefault projected wf => exact ⟨_, .missing absent noDefault, evaluated⟩
    | present defaulted represented => exact ⟨_, .default absent defaulted represented, evaluated⟩

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
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (missingBase : Word) :
    ∃ result finalStore futureWorld,
      ReadResult checked registry functions mapping futureWorld sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates (key :: Transport.carrier header fallback layout entries :: environment) store
        (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore := by
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
    DataMappingHeap.evaluation_preserves_frame heaps actualTyped helperTyped evaluated appended
  exact ⟨result, _, futureWorld, CompatibleExpressionIndices.extend_read_result meaning extension, evaluated, futureHeaps, extension, unchanged⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
