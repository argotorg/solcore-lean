import Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning

/-! The actual closure parameter prefix composes with recursively staged body
meaning. Forward preservation accepts a finite independent staged invocation;
reflection reconstructs that invocation from Core completion. The body IH is
universal over related states, and scope selection is static provenance.
Neither is hidden inside code authenticity or supplied as a child evaluation.
The ordinary decorated-code profile still requires canonical source alignment;
metadata-view body simulation and new source-cell layouts are separate work. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageCalls
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments FunctionCallBody RecursiveStageMeaning

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {registry : Staging.Recursive.Registry} {caller : Staging.Recursive.Scope}
  {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}
  {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
  {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {actual : Environment} {faults : RecursiveStageMeaning.FaultRep}

/-- Parameter allocation is derived from the emitted wrapper. A failure deep
inside the selected body keeps its own scope label and exact mutated heap. -/
theorem preserves
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (bodyMeaning : ∀ child, registry.Closure function child →
      RecursiveStageMeaning.BodyPreserves model program registry child function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {outcome : Staging.Recursive.Outcome}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Staging.Recursive.Applies program registry caller context before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore ∧
      RecursiveStageMeaning.ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have arity : function.parameters.length = arguments.length := by
    rw [← code.artifact.raw.parametersTree.binders, List.length_map]
    exact represented.length.1
  cases execution with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected _ extension allocated executed returned =>
    obtain ⟨entry⟩ := ContractedFunctionCalls.entry_exists layout code extension represented heaps locals
    obtain ⟨rfl, rfl⟩ := allocations_same allocated entry.allocation
    obtain ⟨_, _, typed, _⟩ := frame_body_at code.frame extension
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
      bodyMeaning _ selected code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
        ⟨_, _, executed, returned⟩
    exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, result, finalHeaps,
      entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- A selected authentic body scope is an input of code/value provenance.
Core completion alone then constructs the finite recursive source invocation;
no prior source trace or body evaluation is assumed. -/
theorem reflects
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    {child : Staging.Recursive.Scope} (selected : registry.Closure function child)
    (bodyMeaning : RecursiveStageMeaning.BodyReflects model program registry child function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) {value : Value}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Applies program registry caller context before (.closure function) arguments outcome after ∧
      RecursiveStageMeaning.ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, callContext, _, _, extension, typed, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := ContractedFunctionCalls.entry_exists layout code extension represented heaps locals
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
      (entry.agreement.unwrap evaluated)
  obtain ⟨finalContext, control, executed, returned⟩ := trace
  exact ⟨outcome, after, finalMap, finalWorld,
    .closure selected code.frame extension entry.allocation executed returned,
    result, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
    entry.frame.trans frame, entry.metadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveStageCalls
