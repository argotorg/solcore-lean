import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEntries
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming

/-! Finite evaluation of the actual metadata/default transport wrappers.
Every comparison comes from the real compatible initializer; wrapper children
are value selections. Exact helper allocations remain in the final store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceCoreCompatibleDataEquality DataEquality CompatibleEquality
namespace Transport
abbrev carrier := SourceCoreMappingWithDefault.value

def lookupStore {checked : Checked} (prepared : Prepared checked) (layout : Core.OrderedMapping.Layout)
    (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key : Value) : Store :=
  CompatibleMappingComparison.lookupStore prepared layout (carrier header fallback layout entries :: environment) store entries key

def insertStore {checked : Checked} (prepared : Prepared checked) (layout : Core.OrderedMapping.Layout)
    (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key replacement : Value) : Store :=
  CompatibleMappingComparison.insertStore prepared layout (carrier header fallback layout entries :: environment) store entries key replacement

 theorem expression_weaken {checked : Checked} (prepared : Prepared checked) :
    prepared.expression.weakenAt 0 = prepared.expression := by
  rw [← Expr.rename_insertion]
  exact CoreProof.closed_rename prepared.typed _

 theorem lookup_evaluates {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (CompatibleMappingComparison.KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation} {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : CompatibleMappingComparison.KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (missingBase header : Word) (fallback : Option Value) (mapping keyExpression : Expr)
    (mappingSelected : Selects environment mapping (carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    Evaluates environment store (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mapping keyExpression)
      (SourceCoreMappingWithDefault.selectedValue layout.valueType missingBase header fallback (Core.OrderedMapping.lookupEntries equal key entries))
      (lookupStore prepared layout environment store header fallback entries key) := by
  apply SourceCoreMappingWithDefault.lookup_completed (mappingSelected.evaluates store)
  rw [expression_weaken]
  exact CompatibleMappingComparison.lookup_evaluates prepared layout keyType faithful equal correct keyRep related
    (carrier header fallback layout entries :: environment) store _ _
    (.second (.second (.var rfl))) (keySelected.weaken _)

 theorem insert_evaluates {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (CompatibleMappingComparison.KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation} {sourceKey : Dynamic.Value} {key replacement : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : CompatibleMappingComparison.KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (header : Word) (fallback : Option Value) (mapping keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mapping (carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression replacement) :
    Evaluates environment store (SourceCoreMappingWithDefault.insert layout prepared.expression mapping keyExpression valueExpression)
      (.inRight .word (carrier header fallback layout (Core.OrderedMapping.insertEntries equal key replacement entries)))
      (insertStore prepared layout environment store header fallback entries key replacement) := by
  apply SourceCoreMappingWithDefault.insert_completed (mappingSelected.evaluates store)
  rw [expression_weaken]
  exact CompatibleMappingComparison.insert_evaluates prepared layout keyType faithful equal correct keyRep related
    (carrier header fallback layout entries :: environment) store _ _ _
    (.second (.second (.var rfl))) (keySelected.weaken _) (valueSelected.weaken _)

 theorem lookupStore_extension {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key : Value) :
    ∃ administrative, lookupStore prepared layout environment store header fallback entries key = store ++ administrative ∧
      administrative.length = checked.catalog.entries.length + 1 :=
  CompatibleMappingComparison.helper_store_extension prepared _ _ _ _ _ _

 theorem insertStore_extension {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key replacement : Value) :
    ∃ administrative, insertStore prepared layout environment store header fallback entries key replacement = store ++ administrative ∧
      administrative.length = checked.catalog.entries.length + 1 :=
  CompatibleMappingComparison.helper_store_extension prepared _ _ _ _ _ _

end Transport
end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
