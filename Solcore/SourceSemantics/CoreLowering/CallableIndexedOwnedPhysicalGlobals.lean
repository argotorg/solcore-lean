import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState

/-! The complete physical cache is independent of ordinary Source headers.
Every row keeps its actual installed code, captured environment and unmapped
cell through Source effects and actual frame writes. Method Source authority
is supplied separately by its selected implementation receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveGlobalInitializationMeaning CallableIndexedHistory SourceCoreCallableIndexedFrames

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

abbrev location (compiled : SourceCoreUnifiedCompilation.Compiled) (slot : Nat) : Location :=
  RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals slot

abbrev environment (compiled : SourceCoreUnifiedCompilation.Compiled) : Environment :=
  SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed

/-- Canonical physical references range over actual signatures, including
method signatures. They do not identify a Source callable. -/
def Slots (compiled : SourceCoreUnifiedCompilation.Compiled) (callerPrefix : Nat)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment) : Prop :=
  ∀ slot signature, compiled.indexed.base.globals[slot]? = some signature →
    canonical[scope.length + callerPrefix + slot]? = some
      (.cellRef (OptionalCell.cellType signature.functionType) (location compiled slot))

theorem environment_slots (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Slots compiled 0 [] (environment compiled) := by
  intro slot signature found
  have reference := RecursiveNamedCatalogInitialization.global_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame found
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[slot]? = _ at reference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at reference
  simpa only [List.length_nil, Nat.zero_add, environment, location] using reference

theorem Slots.prepend {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : Slots compiled callerPrefix scope canonical) (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Slots compiled callerPrefix ((id, type) :: scope) (value :: canonical) := by
  intro slot signature found
  have offset : ((id, type) :: scope).length + callerPrefix + slot = scope.length + callerPrefix + slot + 1 := by simp; omega
  rw [offset]
  exact slots slot signature found

theorem Slots.restore {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    (slots : Slots compiled callerPrefix ((id, type) :: scope) (value :: canonical)) :
    Slots compiled callerPrefix scope canonical := by
  intro slot signature found
  have reference := slots slot signature found
  have offset : ((id, type) :: scope).length + callerPrefix + slot = scope.length + callerPrefix + slot + 1 := by simp; omega
  rw [offset] at reference
  exact reference

/-- The actual parameter allocation spine preserves every physical global
reference below the local cells and the single packed-argument slot. -/
theorem Slots.parameters {canonical added : Environment} {scope : SourceCoreLocalCell.Scope}
    (slots : Slots compiled 0 [] canonical) (packed : Value)
    (length : added.length = scope.length) :
    Slots compiled 1 scope (added ++ packed :: canonical) := by
  intro slot signature found
  have offset : scope.length + 1 + slot = added.length + (slot + 1) := by omega
  rw [offset, List.getElem?_append_right (by omega)]
  simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add] using slots slot signature found

/-- Actual physical rows include ordinary functions and selected methods. -/
structure Authority (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (store : Store) : Prop where
  cells : ∀ slot row, (RecursiveNamedCachedRows.rows compiled)[slot]? = some row →
    location compiled slot ∉ mapping ∧
      store.read? (location compiled slot) =
        some (.inRight .unit (installedValue (environment compiled) slot row))

variable {mapping futureMap : LocationMap} {store futureStore : Store}

theorem Authority.extend (authority : Authority compiled mapping store)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    Authority compiled futureMap futureStore := by
  constructor
  intro slot row found
  obtain ⟨unmapped, read⟩ := authority.cells slot row found
  obtain ⟨futureUnmapped, same⟩ := frame _ unmapped (List.getElem?_eq_some_iff.mp read).1
  exact ⟨futureUnmapped, same.trans read⟩

/-- Successful cache extraction retains the whole installed lambda. -/
theorem Authority.cached (authority : Authority compiled mapping store)
    {slot : Nat} {parameter result : Ty} {body : Expr}
    (cached : compiled.indexed.secondPass.closures[slot]? = some (.lambda parameter result body)) :
    location compiled slot ∉ mapping ∧
      store.read? (location compiled slot) = some (.inRight .unit
        (.closure parameter result (body.rename (shift slot).lift)
          (List.replicate slot .unit ++ environment compiled))) := by
  obtain ⟨row, found, same, _⟩ := RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cached
  rcases row with ⟨actualParameter, actualResult, actualBody⟩
  change Expr.lambda parameter result body = Expr.lambda actualParameter actualResult actualBody at same
  cases same
  exact authority.cells slot _ found

/-- A stored lambda cannot be a mutable history frame. -/
theorem Authority.ne_frame (authority : Authority compiled mapping store)
    {slot : Nat} {row : LambdaRow} (found : (RecursiveNamedCachedRows.rows compiled)[slot]? = some row)
    {frameLocation : Location} {native : NativeFrame}
    (frameRead : store.read? frameLocation = some (encode compiled.indexed.ancestry.layout.frame native)) :
    location compiled slot ≠ frameLocation := by
  intro same
  obtain ⟨_, read⟩ := authority.cells slot row found
  rw [← same, read] at frameRead
  cases native <;> simp [encode, installedValue] at frameRead

/-- Replacing the genuine frame preserves every exact cache cell. -/
theorem Authority.install (authority : Authority compiled mapping store)
    {frameLocation : Location} {native : NativeFrame}
    (frameRead : store.read? frameLocation = some (encode compiled.indexed.ancestry.layout.frame native))
    (next : NativeFrame) :
    Authority compiled mapping (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame next)) := by
  have written : store.write? frameLocation (encode compiled.indexed.ancestry.layout.frame next) =
      some (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp frameRead).1, rfl⟩
  constructor
  intro slot row found
  obtain ⟨unmapped, read⟩ := authority.cells slot row found
  exact ⟨unmapped, (Store.write?_preserves_other written (authority.ne_frame found frameRead)).trans read⟩

/-- The real initial store installs all rows, without a semantic Header for
method rows and without assuming a Source body execution. -/
theorem initial (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Authority compiled [] (RecursiveNamedCatalogPreparedInitialization.store compiled) := by
  constructor
  intro slot row found
  have cached : compiled.indexed.secondPass.closures[slot]? = some row.expression := by
    rw [RecursiveNamedCachedRows.exact_cache, List.getElem?_map, found]
    rfl
  obtain ⟨actual, actualFound, _, read⟩ := RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cached
  have same : actual = row := Option.some.inj (actualFound.symm.trans found)
  subst actual
  exact ⟨by simp, read⟩

/-- Successful bootstrap fixes the native store before physical authority is
introduced. This proof does not need an ordinary inventory to cover methods. -/
theorem of_completed {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    Authority compiled [] finalStore := by
  have same := (RecursiveNamedCatalogPreparedInitialization.completed_store accepted completed).2
  rw [same]
  exact initial compiled

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals
