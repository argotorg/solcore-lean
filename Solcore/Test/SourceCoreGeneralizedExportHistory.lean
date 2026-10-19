import Solcore.Test.SourceCoreGeneralizedExportObserved
import Solcore.Test.SourceCoreGeneralizedExportHandleObserved

/-! Concrete exported entries retain their exact independent Source closures.
The complete original inventory and positive materialized history stay attached. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

structure IdentityEntry (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (parameter result : TypeSystem.Ty) where
  entry : Entry
  member : entry ∈ entries
  handleEq : entry.handle = handle
  entryType : entry.sourceType = .function parameter result
  source : TypedSource
  shape : MakeShape source
  definitionContext : SourceSemantics.Context
  captured : Dynamic.Environment
  substitution : TypeSystem.Substitution
  evidence : Dynamic.EvidenceEnvironment
  sourceEq : entry.source = .closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)

def IdentityEntry.append {entries : List Entry} {handle : SourceCorePublicValues.Handle}
    {parameter result : TypeSystem.Ty} (identity : IdentityEntry entries handle parameter result) (added : List Entry) :
    IdentityEntry (entries ++ added) handle parameter result :=
  { identity with member := List.mem_append_left added identity.member }

structure CaptureEntry (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (heap : Dynamic.Heap) (seed : Word) where
  entry : Entry
  member : entry ∈ entries
  handleEq : entry.handle = handle
  entryType : entry.sourceType = .function .bool .word
  source : TypedSource
  shape : CaptureShape source
  definitionContext : SourceSemantics.Context
  captured : Dynamic.Environment
  substitution : TypeSystem.Substitution
  evidence : Dynamic.EvidenceEnvironment
  sourceEq : entry.source = .closure ((shape.principal.descriptor definitionContext captured).instantiate substitution evidence)
  location : Dynamic.Location
  lookup : Dynamic.Environment.LooksUp captured shape.principal.input.id location
  read : Dynamic.Heap.Reads heap location {type := .word, value := some (.word seed)}

structure Context (observed : Observed) where
  whole : WholeInventory observed.fixture
  selected : SelectedInventory whole observed.make
  start : Started observed.fixture.original observed.make.original.key [.bool true]
  first : InitialForward selected observed.makeShape true start observed.callableProfile

variable {observed : Observed} (context : Context observed)
  {artifact : SourceCoreExecution.Artifact}

structure PairHistory (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle : SourceCorePublicValues.Handle) where
  entries : List Entry
  retained : context.first.Retained session entries
  origins : CellAwareMaterializedRetainedEntries.Retained (keys observed.fixture.original.recipe.compiled)
    retained.state.mapping retained.state.world entries
  wordEntry : IdentityEntry entries wordHandle .word .word
  boolEntry : IdentityEntry entries boolHandle .bool .bool

structure FullHistory (session : SourceCoreExecution.Session artifact)
    (wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle) (seed : Word) where
  pair : PairHistory context session wordHandle boolHandle
  captured : CaptureEntry pair.entries captureHandle pair.retained.state.heap seed

/-- Exact selected Source leaves create the two entries used by later calls. -/
theorem Context.collected {executionFuel outputFuel : Nat}
    {returned : SourceCoreExecution.Completion context.start.artifact}
    (resumed : context.start.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    {wordHandle boolHandle : SourceCorePublicValues.Handle}
    (valueEq : returned.value = .product (.function wordHandle) (.function boolHandle)) :
    Nonempty (PairHistory context returned.session wordHandle boolHandle) := by
  have typeEq := context.selected.result_eq.trans observed.makeResult
  let selection := pairSelection typeEq valueEq
  obtain ⟨entries,retained,payload,_handles,selectedLeaves,_heap,materialized⟩ :=
    context.first.observed_materialized observed.typing observed.makeProfile resumed selection
  obtain ⟨firstNative,secondNative,firstType,secondType,remaining,entriesEq⟩ :=
    pair_selected typeEq valueEq selectedLeaves
  subst entries
  let shape := context.selected.make_shape observed.makeShape
  let captured := inputEnvironment shape.principal.input ⟨[]⟩
  refine ⟨⟨_,retained,CellAwareMaterializedRetainedEntries.Retained.of_selected
    (owner observed.fixture.original.recipe.compiled) materialized,?_,?_⟩⟩
  · exact ⟨⟨.function .word .word,
      .closure ((shape.principal.descriptor context.selected.packet.header.context captured).instantiate
        [(shape.principal.typeVariable,.word)]
        (context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.word)])),
      wordHandle,firstNative,firstType,remaining⟩,List.mem_cons_self,rfl,rfl,_,shape,context.selected.packet.header.context,captured,
      [(shape.principal.typeVariable,.word)],
      context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.word)],rfl⟩
  · exact ⟨⟨.function .bool .bool,
      .closure ((shape.principal.descriptor context.selected.packet.header.context captured).instantiate
        [(shape.principal.typeVariable,.bool)]
        (context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.bool)])),
      boolHandle,secondNative,secondType,remaining⟩,List.mem_cons_of_mem _ (List.mem_cons_self),rfl,rfl,_,shape,context.selected.packet.header.context,captured,
      [(shape.principal.typeVariable,.bool)],
      context.selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.bool)],rfl⟩

end Tests.SourceCoreGeneralizedExport
