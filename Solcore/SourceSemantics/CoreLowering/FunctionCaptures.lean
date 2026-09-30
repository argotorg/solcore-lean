import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! Finite capture certificates for generated functions.  A closure keeps
locations, so neither the source nor Core certificate recursively unfolds
heap values.  Source metadata validity is a separate heap-indexed fact; Core
world typing alone does not imply it.  Actual captured layouts retain every
administrative slot, with an explicit renaming from the lexical layout.

This module authenticates locations and types, not function code or calls.
It does not change the legacy input policy or normalize arbitrary captures.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.FunctionCaptures

open Frontend Frontend.SourceInference GeneralHeap

/-- The emitted body is interpreted under the actual captured environment.
The canonical lexical environment is only a proof index. -/
structure Layout (catalog : SourceCoreDataCatalog.Catalog)
    (mapping : LocationMap) (world : Core.StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (source : Dynamic.Environment)
    (actual : Core.Environment) where
  administrativeContext : Core.Context
  canonical : Core.Environment
  actualContext : Core.Context
  embedding : Core.Renaming
  represented : DataHeap.EnvRepresents catalog mapping world administrativeContext scope source canonical
  lookups : Core.ReadOnly.EnvironmentsAgree embedding canonical actual
  types : Core.Renaming.Respects embedding
    (SourceCoreLocalCell.coreContext scope ++ administrativeContext) actualContext
  actualTyped : Core.RuntimeEnvironmentHasTypes world actual actualContext catalog.definitions

variable {catalog : SourceCoreDataCatalog.Catalog} {mapping futureMapping : LocationMap}
  {world futureWorld : Core.StoreTyping} {scope : SourceCoreLocalCell.Scope}
  {source : Dynamic.Environment} {actual : Core.Environment}

def Layout.direct {administrativeContext : Core.Context}
    (represented : DataHeap.EnvRepresents catalog mapping world administrativeContext scope source actual) :
    Layout catalog mapping world scope source actual where
  administrativeContext := administrativeContext
  canonical := actual
  actualContext := SourceCoreLocalCell.coreContext scope ++ administrativeContext
  embedding := Core.Renaming.id
  represented := represented
  lookups := fun found => found
  types := Core.Renaming.respects_id _
  actualTyped := represented.runtime_hasTypes

/-- Extension retains both the actual closure environment and its renaming.
No equality between closures created in different environments is asserted. -/
def Layout.extend (layout : Layout catalog mapping world scope source actual)
    (maps : LocationMap.Extends mapping futureMapping)
    (worlds : Core.WorldExtends world futureWorld) :
    Layout catalog futureMapping futureWorld scope source actual where
  administrativeContext := layout.administrativeContext
  canonical := layout.canonical
  actualContext := layout.actualContext
  embedding := layout.embedding
  represented := layout.represented.extend maps worlds
  lookups := layout.lookups
  types := layout.types
  actualTyped := layout.actualTyped.weaken worlds

theorem Layout.lookup (layout : Layout catalog mapping world scope source actual)
    {id : Resolved.LocalId} {location : Dynamic.Location}
    (found : Dynamic.Environment.LooksUp source id location) :
    ∃ index payload target,
      SourceCoreLocalCell.lookup? scope id = some (index, payload) ∧
      actual[layout.embedding index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨index, payload, target, slot, reference, represented⟩ := layout.represented.lookup_source found
  exact ⟨index, payload, target, slot, layout.lookups reference, represented⟩

/-- The same captured source location remains the same Core location even
when multiple lexical names alias it. -/
theorem references_same_location {location : Dynamic.Location}
    {left right : Core.Location} {leftType rightType : Core.Ty}
    (first : ReferenceRepresents mapping world location left leftType)
    (second : ReferenceRepresents mapping world location right rightType) :
    left = right ∧ leftType = rightType := by
  have same := Option.some.inj (first.mapped.symm.trans second.mapped)
  subst right
  exact ⟨rfl, Core.Ty.sum.inj (Option.some.inj (first.typed.symm.trans second.typed)) |>.2⟩

/-- Strong lexical agreement belongs to the source heap, independently of
the Core representation.  It allows uninitialized cells and shared aliases;
the stored payloads are not required to be eagerly readable values. -/
structure Certificate (catalog : SourceCoreDataCatalog.Catalog)
    (mapping : LocationMap) (world : Core.StoreTyping) (heap : Dynamic.Heap)
    (context : Context) (scope : SourceCoreLocalCell.Scope)
    (source : Dynamic.Environment) (actual : Core.Environment) where
  layout : Layout catalog mapping world scope source actual
  sourceMetadata : Dynamic.EnvironmentAgrees heap context.locals source

def Certificate.extend {heap futureHeap : Dynamic.Heap} {context : Context}
    (certificate : Certificate catalog mapping world heap context scope source actual)
    (metadata : Dynamic.HeapMetadataExtend heap futureHeap)
    (maps : LocationMap.Extends mapping futureMapping)
    (worlds : Core.WorldExtends world futureWorld) :
    Certificate catalog futureMapping futureWorld futureHeap context scope source actual where
  layout := certificate.layout.extend maps worlds
  sourceMetadata := certificate.sourceMetadata.mono metadata

/-- Static lexical lookup recovers the exact source cell metadata and its
mapped reference in the actual closure environment. -/
theorem Certificate.lookup {heap : Dynamic.Heap} {context : Context}
    (certificate : Certificate catalog mapping world heap context scope source actual)
    {id : Resolved.LocalId} {scheme : TypeSystem.Scheme}
    (found : Resolved.LocalScope.Lookup context.locals id scheme) :
    ∃ location cell index payload target,
      Dynamic.Environment.LooksUp source id location ∧
      Dynamic.Heap.Reads heap location cell ∧ cell.type = scheme.body ∧
      Dynamic.LocalCellStorage id scheme cell ∧
      SourceCoreLocalCell.lookup? scope id = some (index, payload) ∧
      actual[certificate.layout.embedding index]? =
        some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨location, cell, lookup, read, type, storage⟩ := certificate.sourceMetadata.lookup found
  obtain ⟨index, payload, target, slot, captured, reference⟩ := certificate.layout.lookup lookup
  exact ⟨location, cell, index, payload, target, lookup, read, type, storage, slot, captured, reference⟩

end Solcore.SourceSemantics.CoreLowering.FunctionCaptures
