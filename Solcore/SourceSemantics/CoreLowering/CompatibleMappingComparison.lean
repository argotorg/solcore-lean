import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning
import Solcore.SourceSemantics.CoreLowering.OrderedMapping

/-! Instantiate the ordinary mapping library with the actual prepared source
comparator. Mathematical predicate witnesses occur only inside proofs. Executed
comparisons use the generated Core closure, whose finite evaluations are
derived from represented keys and installed helper cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMappingComparison
open Core Frontend SourceCoreCompatibleDataEquality DataEquality CompatibleEquality

abbrev KeyRep {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (registry : SourceCoreRawMetadata.Registry) (identities : Dynamic.Value → Word → Prop) :=
  Observation checked.catalog registry identities prepared.type

def comparator {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) : Value :=
  .closure (.product prepared.type prepared.type) .bool
    (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
    (DataEqualityInstalled.captured prepared.bodies.length
      (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment))

def comparisonStore {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) : Store :=
  store ++ DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) prepared.bodies

/-- Two equality observations of the same Core values agree on source
equivalence. This follows from the actual comparator's deterministic finite
execution, without assuming injectivity of unobserved mapping contents/code. -/
theorem equivalent_coherent {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {a b c d : Dynamic.Value} {left right : Value}
    (aRep : KeyRep prepared registry identities a left) (bRep : KeyRep prepared registry identities b right)
    (cRep : KeyRep prepared registry identities c left) (dRep : KeyRep prepared registry identities d right) :
    Dynamic.ValueEquivalent a b ↔ Dynamic.ValueEquivalent c d := by
  have installed := CompatibleEquality.prepared_installed prepared [] []
  obtain ⟨first, firstTree⟩ := prepared_tree prepared aRep bRep [] [] _ installed
  obtain ⟨second, secondTree⟩ := prepared_tree prepared cRep dRep [] [] _ installed
  have same := Value.bool.inj (evaluation_deterministic firstTree.evaluates secondTree.evaluates).1
  exact (firstTree.meaning faithful).symm.trans (same ▸ secondTree.meaning faithful)

theorem exists_predicate_correct {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (registry : SourceCoreRawMetadata.Registry) {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) :
    ∃ equal : Core.OrderedMapping.Predicate,
      OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal := by
  classical
  let equal : Core.OrderedMapping.Predicate := fun left right => decide
    (∃ a b, KeyRep prepared registry identities a left ∧ KeyRep prepared registry identities b right ∧
      Dynamic.ValueEquivalent a b)
  refine ⟨equal, ?_⟩
  constructor
  intro sourceKey sourceStored key stored keyRep storedRep
  simp only [equal, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, aRep, bRep, equivalent⟩
    exact (equivalent_coherent prepared faithful aRep bRep keyRep storedRep).mp equivalent
  · intro equivalent
    exact ⟨_, _, keyRep, storedRep, equivalent⟩

theorem entries_key {keyRel valueRel : OrderedMapping.Relation}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : OrderedMapping.EntriesRel keyRel valueRel sources entries)
    {key value : Value} (member : (key, value) ∈ entries) :
    ∃ sourceKey sourceValue, keyRel sourceKey key ∧ valueRel sourceValue value := by
  induction related with
  | nil => simp at member
  | cons keyRep valueRep tail ih =>
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact ⟨_, _, keyRep, valueRep⟩
    · exact ih remaining

theorem comparisons {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (initialStore store : Store)
    (installed : CompatibleEquality.Installed checked.catalog prepared.bodies initialStore.length environment store) :
    Core.OrderedMapping.Comparisons layout (comparator prepared environment initialStore)
      equal key entries store := by
  intro stored value member
  obtain ⟨sourceStored, _, storedRep, _⟩ := entries_key related member
  obtain ⟨result, meaning, compared⟩ := prepared_compares prepared layout keyType faithful keyRep storedRep
    environment initialStore store installed
  have equivalent := correct.equivalent keyRep storedRep
  have same : result = equal key stored := by
    cases result <;> cases generated : equal key stored <;> simp_all
  subst result
  exact compared

def lookupStore {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key : Value) : Store :=
  Core.OrderedMapping.installedStore (comparisonStore prepared environment store)
    layout.lookupParameter layout.lookupResult (Core.OrderedMapping.lookupBody layout)
    (.pair (Core.OrderedMapping.encode layout entries) (.pair key (comparator prepared environment store))) environment

def insertStore {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key value : Value) : Store :=
  Core.OrderedMapping.installedStore (comparisonStore prepared environment store)
    layout.insertParameter layout.type (Core.OrderedMapping.insertBody layout)
    (.pair (Core.OrderedMapping.encode layout entries) (.pair (.pair key value) (comparator prepared environment store))) environment

theorem lookup_evaluates {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (mapping keyExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) :
    Evaluates environment store (Core.OrderedMapping.lookup layout prepared.expression mapping keyExpression)
      (.inRight .word (Core.OrderedMapping.optionValue layout.valueType
        (Core.OrderedMapping.lookupEntries equal key entries)))
      (lookupStore prepared layout environment store entries key) := by
  apply Core.OrderedMapping.lookup_evaluates entries key (comparator prepared environment store)
    equal (mappingSelected.evaluates store) (keySelected.evaluates store)
    (CompatibleEquality.prepared_evaluates_exact prepared environment store)
  apply comparisons prepared layout keyType faithful equal correct keyRep related
  exact installed_append (CompatibleEquality.prepared_installed prepared environment store) _

theorem insert_evaluates {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key value : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (mapping keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression value) :
    Evaluates environment store (Core.OrderedMapping.insert layout prepared.expression mapping keyExpression valueExpression)
      (.inRight .word (Core.OrderedMapping.encode layout
        (Core.OrderedMapping.insertEntries equal key value entries)))
      (insertStore prepared layout environment store entries key value) := by
  apply Core.OrderedMapping.insert_evaluates entries key value (comparator prepared environment store)
    equal (mappingSelected.evaluates store) (keySelected.evaluates store)
    (valueSelected.evaluates store) (CompatibleEquality.prepared_evaluates_exact prepared environment store)
  apply comparisons prepared layout keyType faithful equal correct keyRep related
  exact installed_append (CompatibleEquality.prepared_installed prepared environment store) _

/-- A helper appends comparator cells followed by exactly one recursive
mapping helper cell. Existing source and administrative cells are unchanged. -/
theorem helper_store_extension {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) (parameter result : Ty) (body : Expr) (input : Value) :
    ∃ administrative,
      Core.OrderedMapping.installedStore (comparisonStore prepared environment store) parameter result body input environment =
        store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  refine ⟨DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) prepared.bodies ++
    [.inRight .unit (Core.WordMapping.closure parameter result body
      (comparisonStore prepared environment store).length (input :: environment))], ?_, ?_⟩
  · simp [Core.OrderedMapping.installedStore, Core.WordMapping.installedStore, comparisonStore, List.append_assoc]
  · simp [DataEqualityInstalled.cells, CompatibleEquality.bodies_length prepared.bodiesGenerated]

end Solcore.SourceSemantics.CoreLowering.CompatibleMappingComparison
