import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyMeaning

/-! Exact lexical exits for staged bodies that keep their initial context.
Discard-sequence body bounds already return map/world and Source metadata
extensions. Those concrete receipts construct the unchanged lexical witness;
the original staged trace supplies ordinary control independently. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyExitReceipts
open Core Frontend SourceInference GeneralHeap

variable {checked : SourceCoreCompatibleCatalog.Checked} {definitions : DataEnvironment}
  {mapping finalMap : LocationMap} {world finalWorld : StoreTyping} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {environment : Dynamic.Environment} {canonical : Environment} {before after : Dynamic.Heap}

/-- The actual body extensions validate the unchanged original lexical scope. -/
theorem lexical_unchanged
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after) (owner : Resolved.DeclarationId) :
    TypedStatementMixed.LexicalResult checked definitions finalMap finalWorld administrative owner
      context scope environment context after :=
  ⟨scope, environment, canonical, .here, environments.extend maps worlds, locals.mono metadata⟩

variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {function : Dynamic.Closure}

/-- Successful staged control and genuine selected provenance construct the
full lexical exit expected by the existing parameter and invocation consumers. -/
theorem reached_returned
    (selected : stages.Closure function invocation)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after)
    {resultContext : SourceSemantics.Context} {value : Dynamic.Value}
    (sameContext : resultContext = context)
    (trace : Staging.Recursive.Statements program stages invocation context environment before
      function.body resultContext (.returned value) after) :
    TypedMixedNamedBody.ReachedExit checked definitions finalMap finalWorld administrative
      program function context scope environment before after (.value value) := by
  subst resultContext
  refine ⟨context, .returned value, .control ?_, .returned value,
    lexical_unchanged environments locals maps worlds metadata function.source.owner⟩
  simpa only [stages.source selected, stages.evidence selected] using trace.returned_plain

/-- Ordinary semantic failure retains the same lexical receipt and prefix heap.
Stage rejection is excluded by the literal semantic outcome constructor. -/
theorem reached_semanticFault
    (selected : stages.Closure function invocation)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after)
    {resultContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (sameContext : resultContext = context)
    (trace : Staging.Recursive.Statements program stages invocation context environment before
      function.body resultContext (.fault (.semantic reason)) after) :
    TypedMixedNamedBody.ReachedExit checked definitions finalMap finalWorld administrative
      program function context scope environment before after (.fault reason) := by
  subst resultContext
  refine ⟨context, .fault reason, .fault ?_, .fault reason,
    lexical_unchanged environments locals maps worlds metadata function.source.owner⟩
  simpa only [stages.source selected, stages.evidence selected] using trace.semanticFault_plain

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyExitReceipts
