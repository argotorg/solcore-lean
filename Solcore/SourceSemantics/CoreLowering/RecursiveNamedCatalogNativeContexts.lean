import Solcore.SourceSemantics.CoreLowering.NativeExpressionContextSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileAllocation

/-! Cached code typing is moved to the real canonical body environment using
an authenticated global inventory and a checked free-slot bound. Runtime value
types identify reference slots; the body's typing comes from the actual cached
code, not from those value types. The ordinary named capture prefix is zero.
Unused wrapper inputs remain arbitrary on both sides. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open NativeExpressionContextSupport

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- Every cached global has the same actual slot and complete signature in the
finite semantic inventory. Duplicates are not reordered or silently removed. -/
def Complete (headers : Inventory prepared values ambient.definitions program) : Prop :=
  ∀ index signature, base.globals[index]? = some signature →
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature

def bodyScope (header : Header prepared values ambient.definitions program) : SourceCoreLocalCell.Scope :=
  header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))

def bodyPrefix (header : Header prepared values ambient.definitions program) : Core.Context :=
  SourceCoreLocalCell.coreContext (bodyScope header) ++
    SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) ::
    base.globals.map (·.referenceType) ++ [.cell prepared.layout.frame.type]

/-- The exact cached lambda and real marked parameter action fix the body code
and parameter types before any environment transport. -/
theorem body_of_cached {header : Header prepared values ambient.definitions program}
    {suffix : Core.Context}
    (typed : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions) :
    HasType (bodyPrefix header ++ suffix) header.body (LanguageResult.resultType header.output) ambient.definitions := by
  cases typed with
  | lambda parameterWF resultWF codeTyped =>
    obtain ⟨_, _, _, _, emitted⟩ := CallableIndexedFormation.namedBody_receipt prepared header.hook
    rw [emitted] at codeTyped
    have parameters := CallableIndexedParameterNativeInversion.withFrame_body codeTyped
    have body := CallableIndexedParameterNativeInversion.accepted_body header.onError header.acceptedPrefix parameters
    rw [CallableIndexedParameterNativeInversion.final_context] at body
    simpa only [bodyPrefix, bodyScope, header.parameterType, header.resultType,
      List.append_assoc, List.cons_append, List.nil_append] using body

/-- Preparation supplies the native proof from its checked assembled entry.
The cached-row equation identifies the header's exact lambda. -/
theorem prepared_body {initial : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {indexed : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare initial fuel = .ok indexed)
    {entry : SourceCoreCallableIndexedPrograms.Entry indexed.layouts} (member : entry ∈ indexed.entries)
    {values : ValuesContext} {program : Program}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (definitions : ambient.definitions = indexed.layouts.definitions)
    (header : Header indexed.ancestry values ambient.definitions program)
    (cached : indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code))
    (global : indexed.base.globals[header.slot]? = some header.named.signature) :
    HasType (bodyPrefix header ++ SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      header.body (LanguageResult.resultType header.output) ambient.definitions := by
  apply body_of_cached
  simpa only [← definitions] using CallableIndexedCachedNativeTyping.prepared_native_closure accepted member cached global

variable {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {header : Header prepared values ambient.definitions program}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}

/-- The real entry fixes every used reference type, including the shared
frame. No equality is required of the unused administrative suffix. -/
theorem entry_prefix (complete : Complete headers)
    (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (suffix : Core.Context) :
    Agrees (bodyPrefix header).length (bodyPrefix header ++ suffix)
      (SourceCoreLocalCell.coreContext (bodyScope header) ++
        SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) := by
  let localTypes := SourceCoreLocalCell.coreContext (bodyScope header)
  let bundle := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd)
  have localLength : localTypes.length = header.bindings.length := by
    simp [localTypes, SourceCoreLocalCell.coreContext, bodyScope]
  have tag {index : Nat} {value : Value} (found : entry.canonical[index]? = some value) :
      (localTypes ++ bundle :: administrative)[index]? = some value.type := by
    have types := entry.environments.runtime_hasTypes.type_tags
    change entry.canonical.map Value.type = localTypes ++ bundle :: administrative at types
    rw [← types]
    simp [found]
  intro index smaller
  change (localTypes ++ bundle :: administrative)[index]? =
    (localTypes ++ bundle :: base.globals.map (·.referenceType) ++ [.cell prepared.layout.frame.type] ++ suffix)[index]?
  by_cases localSlot : index < localTypes.length
  · simp [List.getElem?_append, localSlot]
  · let offset := index - localTypes.length
    have indexEq : index = localTypes.length + offset := by omega
    rw [indexEq]
    have prefixLength : (bodyPrefix header).length = localTypes.length + base.globals.length + 2 := by simp [bodyPrefix, localTypes]; omega
    rw [prefixLength] at smaller
    have offsetBound : offset < base.globals.length + 2 := by omega
    cases offsetEq : offset with
    | zero => simp [List.getElem?_append]
    | succ slot =>
      have bound : slot < base.globals.length + 1 := by omega
      have outside : ¬ localTypes.length + (slot + 1) < localTypes.length := by omega
      by_cases globalSlot : slot < base.globals.length
      · let signature := base.globals[slot]
        have selected : base.globals[slot]? = some signature := List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
        obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
        have found := entry.catalog.globals target member
        have idx : (bodyScope header).length + (0 + 1) + target.slot = localTypes.length + (slot + 1) := by
          simp only [bodyScope, List.length_map, List.length_reverse, localLength, sameSlot]; omega
        change entry.canonical[(bodyScope header).length + (0 + 1) + target.slot]? = _ at found
        have typed := tag found
        rw [idx] at typed
        simpa [List.getElem?_append, outside, globalSlot, selected, signature,
          sameSignature, SourceCoreCalls.Signature.referenceType, OptionalCell.referenceType, Value.type] using typed
      · have last : slot = base.globals.length := by omega
        have typed := tag entry.reference
        have idx : header.bindings.length + 1 + header.globals = localTypes.length + (slot + 1) := by omega
        rw [idx] at typed
        simpa [List.getElem?_append, outside, last, Value.type] using typed

/-- The support receipt concerns this exact emitted body. In particular,
no arbitrary administrative-context native typing is an input. -/
theorem canonical_body {suffix : Core.Context}
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (typed : HasType (bodyPrefix header ++ suffix) header.body (LanguageResult.resultType header.output) ambient.definitions)
    (support : supported header.body (bodyPrefix header).length = true)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  typing typed support (entry_prefix complete globals entry suffix)

/-- A support check on the actual cached lambda also bounds the emitted
body. First remove only the unused wrapper suffix syntactically, then invert
the real hook and allocation actions. -/
theorem canonical_cached {suffix : Core.Context}
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions := by
  have original : HasType ((base.globals.map (·.referenceType) ++ [.cell prepared.layout.frame.type]) ++ suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions := by simpa using cachedTyped
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original (by simpa using support)
  have body := body_of_cached (suffix := []) (by simpa using minimal)
  have bodySupport : supported header.body (bodyPrefix header).length = true := by
    simpa using of_typing body
  exact canonical_body complete globals body bodySupport entry

/-- The real entry embedding transports that syntax proof to the actual
parameter environment; no captured environment or closure is rewritten. -/
theorem actual_body {suffix : Core.Context}
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (typed : HasType (bodyPrefix header ++ suffix) header.body (LanguageResult.resultType header.output) ambient.definitions)
    (support : supported header.body (bodyPrefix header).length = true)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    HasType (CallableIndexedParameterTyped.prefixContext header.bindings actualContext)
      (header.body.rename entry.embedding) (LanguageResult.resultType header.output) ambient.definitions := by
  exact (canonical_body complete globals typed support entry).rename
    (TypedLexicalWhile.environment_respects entry.environments.runtime_hasTypes entry.actualTyped entry.lookups)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
