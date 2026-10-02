import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.Header.certificate
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.Profile.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ParameterEntry.mk

/-! Static header/profile separation and real all-target parameter entry.
Formal consumers require actual captured reference coherence; no body meaning
or source/native body execution is an input. Checked cached runs exercise self
and mutual globals under imperative bodies, faults and native resume. They do
not establish the deferred mutually recursive correspondence theorem. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalog
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterMeaning
section Foundation
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store}

/-- This final prefix consumer exposes every actual global reference in the
callee body environment. The only independent runtime inputs are represented
arguments, the initial heap and the retained installed catalog. -/
theorem all_targets_after_named_prefix
    (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      ∃ capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store,
        ∃ entry : ParameterEntry headers locations capturePrefix functions registry header arguments heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) mapping world
          capture.administrative
          (.unit :: prepared.layout.frame.type :: header.named.signature.parameterType :: capture.capturedContext)
          (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured)
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
          authority.frameLocation (.state index) (.named origin),
          ∀ target, target ∈ headers →
            entry.actualBody[entry.embedding (header.bindings.length + (capturePrefix + 1) + target.slot)]? = some
              (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target)) := by
  obtain ⟨origin, index, metadata, owned, history, _, capture, ⟨entry⟩⟩ := named_parameters authority member represented heaps
  refine ⟨origin, index, metadata, owned, history, capture, entry, ?_⟩
  intro target targetMember
  simpa only [List.length_map, List.length_reverse] using entry.lookups (entry.catalog.globals target targetMember)

/-- Native typing alone cannot replace a missing capture reference. -/
theorem missing_capture_rejected {header target : Header prepared values ambient.definitions program} {location : Location}
    (capture : Capture headers locations capturePrefix location header mapping world heap store)
    (member : target ∈ headers)
    (missing : capture.canonical[capturePrefix + target.slot]? = none) : False := by
  have exactReference := capture.coherent target member
  rw [missing] at exactReference
  cases exactReference

/-- All closures remain exact after actual argument-prefix effects. -/
theorem target_after_prefix {scope : Scope} {canonical actual : Environment} {ξ : Renaming}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    {futureMap : LocationMap} {futureWorld : StoreTyping} {after : Dynamic.Heap} {futureStore : Store}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers) (reason : Word) :
    ∃ capture : Capture headers locations capturePrefix entry.authority.frameLocation header futureMap futureWorld after futureStore,
      Evaluates actual futureStore (OptionalCell.read header.named.signature.functionType
        (.var (ξ (scope.length + callerPrefix + header.slot))) reason)
        (.inRight .word (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)) futureStore :=
  (entry.extend maps worlds frame metadata).read_target agrees member reason

end Foundation

private def content : String := String.intercalate "\n" [
  "function self(n: Word) returns (Word) { if (n == 0) { return 2; } let total = 0; for (let i = 0; i < 2; i += 1) { total += self(n - 1); } return total; }",
  "function left(n: Word) returns (Word) { return n == 0 ? 7 : right(n - 1); }",
  "function right(n: Word) returns (Word) { let i = n; while (i != 0) { i -= 1; return left(i); } return 11; }",
  "function driver(n: Word) returns (Word) { let f = left; let total = self(2); for (let i = 0; i < n; i += 1) { total += f(i); } return total; }",
  "function fail(n: Word) returns (Word) { let written = self(n); let gap: Word; return gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word n)

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named catalog" content ["self", "left", "right", "driver", "fail"]
  SourceCoreUnifiedCorpusSupport.assertTrue (compiled.indexed.base.functions.length == 5)
    "recursive catalog changed the finite named inventory"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (compiled.indexed.secondPass.closures.length == compiled.indexed.base.functions.length)
    "recursive catalog cached slots are incomplete"
  for (name, argument, expected) in [("self", 3, 16), ("left", 2, 7), ("right", 2, 11), ("driver", 3, 33)] do
    for fuel in [0, 7, 83] do
      let _ ← SourceCoreUnifiedCorpusSupport.expect compiled name [w argument] (w expected) fuel
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled "fail" [w 2]
  match first.observation with
  | .fault (.uninitializedLocal _) state =>
    SourceCoreUnifiedCorpusSupport.assertTrue (SourceCoreUnifiedCorpusSupport.hasWord state 8)
      "recursive catalog fault lost completed recursive writes"
    for fuel in [0, 7, 83] do
      let start ← SourceCoreUnifiedCorpusSupport.execute compiled "fail" [w 2] fuel
      let resumed ← SourceCoreUnifiedCorpusSupport.get "recursive catalog fault resume" (start.resume 300000)
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr resumed.observation == reprStr first.observation)
        "recursive catalog fault resume changed source observations"
  | other => throw (IO.userError s!"recursive catalog expected first uninitialized fault: {reprStr other}")
  IO.println "recursive named catalog: static headers/profiles, all-target prefix receipts, captured coherence, self/mutual globals, imperative bodies, fault writes and resume GREEN"
end Tests.SourceCoreRecursiveNamedCatalog
