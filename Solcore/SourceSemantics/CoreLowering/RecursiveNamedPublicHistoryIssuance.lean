import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.Frontend.SourceCoreExecution

/-! Public issuance extends the semantic history attached to the same actual
session. The returned completion preserves the exact indexed handle and
current caller, ready for the existing history input and execution theorems. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (Entry History Caller)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

private theorem indexed_artifact_eq
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {leftArtifact rightArtifact : SourceCoreIndexedSession.Artifact}
    {left : SourceCoreIndexedSession.Session leftArtifact} {right : SourceCoreIndexedSession.Session rightArtifact}
    (first : session.IndexedAt left) (second : session.IndexedAt right) : leftArtifact = rightArtifact := by
  rcases artifact with ⟨compilation, opened⟩
  cases opened with
  | empty selected => exact False.elim first
  | indexed recipe selected native atRecipe =>
      cases session
      exact first.1.symm.trans second.1

/-- The public named issuance supplies the exact new entry at the existing
current caller, without a representation or Source typing premise. -/
theorem named_remembered
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {nativeArtifact : SourceCoreIndexedSession.Artifact} {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
    {entries : List Entry} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller (headers rows) (keys compiled) mapping world heap store}
    {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (history : History (headers rows) (keys compiled)
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
      registry anchor nativeSession mapping world heap store caller entries)
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {publicArtifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session publicArtifact}
    (atSession : session.IndexedAt nativeSession)
    {issued : SourceCoreExecution.Completion publicArtifact} {issuanceFuel : Nat}
    (issuance : session.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    {handle : Handle} (handleValue : issued.value = .function handle)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact) (native : Core.Value),
      issued.IndexedAt actual ∧
      History (headers rows) (keys compiled)
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor actual.session mapping world heap store caller
        (entries ++ [⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global
            packet.header.named.specialized input.prepared.available)), handle, native,
          CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType,
          issuanceFuel⟩]) := by
  obtain ⟨actualArtifact, before, actual, beforeAt, actualIssuance, completedAt⟩ := issuance
  have sameArtifact := indexed_artifact_eq atSession beforeAt
  cases sameArtifact
  have sameSession := atSession.unique beforeAt
  cases sameSession
  obtain ⟨native, extended⟩ := History.remember_named prepared inputs rows packet member
    bodyRegistry registry faults profile history actualIssuance atRecipe
    (completedAt.1.symm.trans handleValue) wellFormed
  exact ⟨actual, native, completedAt, extended⟩

/-- The public builtin issuance joins the same history and leaves its native
and Source heaps unchanged, retaining all earlier exported closures. -/
theorem builtin_remembered
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {nativeArtifact : SourceCoreIndexedSession.Artifact} {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
    {entries : List Entry} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store}
    {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (history : History headers keys
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      registry anchor nativeSession mapping world heap store caller entries)
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {publicArtifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session publicArtifact}
    (atSession : session.IndexedAt nativeSession)
    {issued : SourceCoreExecution.Completion publicArtifact} {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : session.BuiltinIssuedAt function issuanceFuel issued)
    {handle : Handle} (handleValue : issued.value = .function handle) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact) (native : Core.Value),
      issued.IndexedAt actual ∧
      History headers keys
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor actual.session mapping world heap store caller
        (entries ++ [⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function),
          issuanceFuel⟩]) := by
  obtain ⟨actualArtifact, before, actual, beforeAt, actualIssuance, completedAt⟩ := issuance
  have sameArtifact := indexed_artifact_eq atSession beforeAt
  cases sameArtifact
  have sameSession := atSession.unique beforeAt
  cases sameSession
  obtain ⟨native, extended⟩ := History.remember_builtin prepared headers keys bodyRegistry registry faults profile
    history actualIssuance atRecipe (completedAt.1.symm.trans handleValue)
  exact ⟨actual, native, completedAt, extended⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
