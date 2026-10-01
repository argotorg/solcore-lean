import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualMembers
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning

/-! Scalar-key index helpers use the real generated comparator. No callable
identity law is needed for Bool, Word, or Integer keys. Administrative closures
are typed using the full actual environment and actual ambient definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend CompatiblePayload CompatibleMapping CompatibleEquality DataEquality
open GeneralHeap ReadOnly CompatibleExpressionPrimitives

inductive Scalar : Ty → Prop where
  | bool : Scalar .bool
  | word : Scalar .word
  | integer : Scalar .integer

private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem noIdentities_faithful : IdentityFaithful noIdentities :=
  ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem Scalar.observation {type : Ty} (scalar : Scalar type)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    Observation checked.catalog registry noIdentities type source value := by
  cases scalar with
  | bool => obtain ⟨value, rfl, rfl⟩ := bool_fields related; exact .bool value
  | word => obtain ⟨value, rfl, rfl⟩ := word_fields related; exact .word value
  | integer => obtain ⟨value, rfl, rfl⟩ := integer_fields related; exact .integer value

private theorem scalar_entries (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {keyType valueType : Ty} (scalar : Scalar keyType) (projected : keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    CoreLowering.OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry noIdentities)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  subst keyType
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value rest => exact .cons (scalar.observation key) value (ih rest)

/-- Total finite lookup from scalar key receipts, using actual prepared code. -/
theorem lookup_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {layout : Core.OrderedMapping.Layout} (scalar : Scalar layout.keyType) (keyType : layout.keyType = prepared.type)
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
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry noIdentities_faithful
  have fullCorrect : CoreLowering.OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey layout.keyType) equal := by
    refine ⟨fun left right => correct.equivalent ?_ ?_⟩
    · simpa only [keyType] using scalar.observation left
    · simpa only [keyType] using scalar.observation right
  have observed : CompatibleMappingComparison.KeyRep prepared registry noIdentities sourceLookup key := by
    simpa only [keyType] using scalar.observation keyRep
  have evaluated := Transport.lookup_evaluates prepared layout keyType noIdentities_faithful equal correct observed
    (scalar_entries prepared scalar keyType fields.stored) environment store missingBase header fallback
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

theorem extend_read_result {sourceValue : TypeSystem.Ty} {sourceLookup : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {type : Ty} {missingBase header : Word} {result : Value}
    (related : ReadResult checked registry functions mapping world sourceValue sourceLookup sources type missingBase header result)
    {futureWorld : StoreTyping} (extension : WorldExtends world futureWorld) :
    ReadResult checked registry functions mapping futureWorld sourceValue sourceLookup sources type missingBase header result := by
  cases related with
  | found selected represented => exact .found selected (represented.extend (.refl _) (.refl _) extension)
  | default absent defaulted represented => exact .default absent defaulted (represented.extend (.refl _) (.refl _) extension)
  | missing absent unavailable => exact .missing absent unavailable

private theorem closed_hasType {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) : HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

/-- Comparator closure allocations preserve the source heap and every existing
administrative cell. The captured actual slots must all be typed. -/
theorem lookup_preserves_heap (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {layout : Core.OrderedMapping.Layout} (scalar : Scalar layout.keyType) (keyType : layout.keyType = prepared.type)
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
  obtain ⟨result, meaning, evaluated⟩ := lookup_meaning prepared scalar keyType fields keyRep
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
  exact ⟨result, _, futureWorld, extend_read_result meaning extension, evaluated, futureHeaps, extension, unchanged⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
