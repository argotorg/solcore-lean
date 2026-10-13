import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralLambdaValues

/-! A positive named handle retains the actual installed capture, including
method slots. Equal code alone does not identify its captured environment. The
receipt survives map/world growth and reconstructs the same physical capture
at call time from genuine cache authority. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNamedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedCapture NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedPhysicalGlobals

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {sourceType : TypeSystem.Ty} {function : Dynamic.GlobalFunction} {native : Value} {type : Ty}

structure Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (function : Dynamic.GlobalFunction) (native : Value) (type : Ty) where
  owner : OwnedKey keys
  header : Header compiled (Program.ofChecked compiled.sourceProgram)
  rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment
  identity : Word
  capture : NamedCapture headers owner.key header mapping world
  descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key)
  member : header ∈ headers
  sourceAt : NamedSourceAt header rawD function
  installed : NamedInstalledCode capture
  number : Word.ofNat? (header.slot + 1) = some identity
  projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
    (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType)
    (header.code.rename capture.embedding.lift) capture.captured)
    header.named.signature.functionType compiled.indexed.layouts.definitions
  canonical_eq : capture.canonical = environment compiled
  captured_eq : capture.captured = List.replicate header.slot .unit ++ environment compiled
  embedding_eq : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot
  sourceType_eq : sourceType = header.named.specialized.function.type
  native_eq : native = .pair (.pair (.inRight .unit (.word identity))
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id)
  type_eq : type = CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType

variable (association : Association headers keys mapping world sourceType function native type)

/-- Extension keeps the exact original installed environment and code. -/
def Association.extend (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    Association headers keys futureMap futureWorld sourceType function native type :=
  { association with capture := association.capture.extend maps worlds, typed := association.typed.weaken worlds }

include association in
/-- Forward erasure is used for existing callable classification only. -/
theorem Association.represents {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      sourceType (.global function) native type := by
  rcases association with ⟨owner, header, rawD, identity, capture, descriptor, member, sourceAt,
    installed, number, projection, typed, _canonical, _captured, _embedding, sourceEq, nativeEq, typeEq⟩
  subst sourceType native type
  exact .prior (.prior (.named owner member sourceAt capture installed number projection descriptor typed))


/-- Actual installed captures produce positive named handles without inferring
capture identity from native typing or ordinary Header coverage. -/
def of_capture
    (owner : OwnedKey keys) (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    {store : Store} (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} (sourceAt : NamedSourceAt header rawD function)
    (member : header ∈ headers) (installed : NamedInstalledCode capture.named)
    (identity : Word) (number : Word.ofNat? (header.slot + 1) = some identity)
    (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.named.embedding.lift) capture.named.captured)
      header.named.signature.functionType compiled.indexed.layouts.definitions) :
    Association headers keys mapping world header.named.specialized.function.type function
      (.pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.named.embedding.lift) capture.named.captured)) (.word descriptor.id))
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) :=
  ⟨owner, header, rawD, identity, capture.named, descriptor, member, sourceAt, installed, number,
    projection, typed, capture.canonical_eq, capture.captured_eq, capture.embedding_eq, rfl, rfl, rfl⟩

/-- The real cache receipt gives the same retained closure at this later store. -/
theorem Association.at_store {store : Store}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation association.header)
    (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical association.owner.key headers)
    (physical : Authority compiled mapping store) :
    Nonempty { capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers association.owner.key
        association.header mapping world store // capture.named = association.capture } := by
  have cached : compiled.indexed.secondPass.closures[association.header.slot]? = some
      (.lambda association.header.named.signature.parameterType
        (LanguageResult.resultType association.header.named.signature.resultType) association.header.code) := by
    rw [aligned.slot, aligned.named, aligned.code]
    exact prepared.cached.trans (congrArg some prepared.compilation.emitted)
  have read := (physical.cached cached).2
  have actualRead : store.read? (association.owner.key.locations association.header) = some (.inRight .unit
      (.closure association.header.named.signature.parameterType
        (LanguageResult.resultType association.header.named.signature.resultType)
        (association.header.code.rename association.capture.embedding.lift) association.capture.captured)) := by
    rw [keyPhysical.locations _ association.member, association.embedding_eq, association.captured_eq]
    exact read
  exact ⟨⟨⟨keyPhysical, association.capture, actualRead, association.canonical_eq, association.captured_eq,
    association.embedding_eq, by rw [association.canonical_eq]; exact environment_slots compiled⟩, rfl⟩⟩

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (function : Dynamic.GlobalFunction) (native : Value) (type : Ty) : Prop :=
  Nonempty (Association headers keys mapping world sourceType function native type)

theorem StaticMember.represents {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (member : StaticMember headers keys mapping world sourceType function native type) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      sourceType (.global function) native type := by
  obtain ⟨association⟩ := member
  exact association.represents

theorem StaticMember.extend (member : StaticMember headers keys mapping world sourceType function native type)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys futureMap futureWorld sourceType function native type := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNamedAssociation
