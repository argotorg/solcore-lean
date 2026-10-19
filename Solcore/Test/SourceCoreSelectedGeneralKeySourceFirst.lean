import Solcore.Test.SourceCoreSelectedGeneralKeyFixture
import Solcore.Test.SourceCoreSelectedGeneralKeyWriteSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicInitialData

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

/-- Actual compiler selection and fresh bootstrap determine the public issuer
and original source. No body execution or completed public call is assumed. -/
structure Selection {fixture : CompiledFixture} (row : Row fixture)
    {arguments : List SourceCorePublicValues.Value} (started : Started fixture row.original.key arguments) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = row.original.function.typedBody

theorem selection {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {arguments : List SourceCorePublicValues.Value} (started : Started fixture row.original.key arguments) :
    Nonempty (Selection row started) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) eligible
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  exact ⟨⟨issued, initial, sourceEq⟩⟩

/-- The final public conclusion retains the whole Source value, authentic
encoding and retained history, or an actual earlier stage rejection. -/
structure InitialOutput {fixture : CompiledFixture} (row : Row fixture)
    {publicArguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.original.key publicArguments)
    (arguments : List Dynamic.Value) (value : Dynamic.Value) (after : Dynamic.Heap) extends Selection row started where
  plain : ∀ invocation, RecursiveNamedPublicPhysicalSessionState.PlainValue
    initial.header initial.header invocation ⟨[]⟩ arguments value after
  forward : ∀ invocation,
    (SelectedCompilationPublicSessionState.SourceCall initial.header initial.header invocation
        ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header issued.initial
        issued.support.profile fixture.recipe [] initial.header.function.resultType started.call.checkpoint value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation arguments

def Key.carrier : Key → SourceCoreDataValues.Value
  | .pair left right => .product (.bool left) (.bool right)
  | .proxy inner => .proxy inner
  | .nominal metadata argument => .constructed metadata [.bool argument]

def entries (key : Key) (first later : Word) : List (Dynamic.Value × Dynamic.Value) :=
  [(key.value,.word first),(key.value,.word later)]
def mapCarrier (key : Key) (first later : Word) : SourceCoreDataValues.Value :=
  .mapping key.type .word [(key.carrier,.word first),(key.carrier,.word later)]
def publicMap (key : Key) (first later : Word) : SourceCorePublicValues.Value :=
  SourceCoreIndexedSession.DataInput.publicValue (mapCarrier key first later)

theorem Key.means (key : Key) : DataPayloadEncoding.Means key.carrier key.value := by
  cases key with
  | pair left right => exact .product (.bool left) (.bool right)
  | proxy inner => exact .proxy inner
  | nominal metadata argument => exact .constructed (.cons (.bool argument) .nil)

theorem KeyNode.input_typed {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context : SourceSemantics.Context} (valid : key.Valid context) :
    RecursiveNamedPublicDataArgumentReceipts.DataTyped context key.carrier key.type := by
  cases node.shape with
  | pair => exact .product (.bool _) (.bool _)
  | proxy => exact .proxy _
  | nominal child _ _ payload =>
    exact .constructed valid (by rw [payload]; exact .cons (.bool _) .nil)

private theorem key_valid_at {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context target : SourceSemantics.Context} (valid : key.Valid context)
    (same : context.signatures = target.signatures) : key.Valid target := by
  cases node.shape with
  | pair | proxy => trivial
  | nominal _ _ substitution _ =>
    cases valid with
    | intro dataType signature dataMember signatureMember owner constructorEq exact range payload result =>
      exact .intro dataType signature (by rw [← same]; exact dataMember) signatureMember owner constructorEq exact
        (by rw [substitution]; intro parameter replacement impossible; cases impossible) payload result

private theorem cast_right {source target : TypedSource} {key : Key} (same : source = target)
    (shape : WriteShape source key) :
    (same ▸ shape).right.resolution.rawValue = shape.right.resolution.rawValue := by cases same; rfl

theorem map_meanings (key : Key) (first later : Word) :
    RecursiveNamedPublicDataInputs.Meanings [publicMap key first later]
      [mappingValue key (entries key first later)] := by
  exact .cons ⟨mapCarrier key first later,rfl,
    .mapping (.prepend key.means (.word first) (.prepend key.means (.word later) .empty))⟩ .nil

theorem map_types {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context : SourceSemantics.Context} (valid : key.Valid context) (first later : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes context [publicMap key first later] [mappingType key] := by
  exact .cons ⟨mapCarrier key first later,rfl,
    .mapping (.entry (node.input_typed valid) (.word first)
      (.entry (node.input_typed valid) (.word later) (.empty _ _)))⟩ .nil

/-- The checker, full compile receipt and startup produce the actual public
issuer. Original ordered key execution is established before public completion. -/
theorem read_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {key : Key} (shape : ReadShape row.original.function.typedBody key)
    (first later : Word) (started : Started fixture row.original.key [publicMap key first later]) :
    Nonempty (InitialOutput row started [mappingValue key (entries key first later)] (.word first)
      (mappingHeap ⟨[]⟩ key (entries key first later))) := by
  obtain ⟨chosen⟩ := selection row profile started
  have actual : ReadShape chosen.initial.header.function.source key := by rw [chosen.sourceEq]; exact shape
  have certified := chosen.issued.support.certificates chosen.initial.header chosen.initial.start.selected.member
  obtain ⟨rawD,global,sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => read_plain chosen.initial.header actual certified sourceAt
    chosen.initial.header invocation ⟨[]⟩ first [(key.value,.word later)]
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [publicMap key first later] chosen.initial.header.types := by
    rw [read_input_types chosen.initial.header actual]
    exact map_types actual.keyNode
      (key_valid_at actual.keyNode (read_key_valid chosen.initial.header actual certified)
        (Dynamic.MonoBindersExtend.runtimeContextFields chosen.initial.header.extended).signatures) first later
  exact ⟨{
    toSelection := chosen
    plain := by simpa only [entries] using plain
    forward := fun invocation => by
      simpa only [entries] using chosen.initial.forward_data_output_plain types (map_meanings key first later) (plain invocation) }⟩

/-- Compound update preserves later duplicate entries and returns the complete
mapping representation, from a fresh metadata-bearing public input. -/
theorem write_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {key : Key} (shape : WriteShape row.original.function.typedBody key)
    (first later : Word) (started : Started fixture row.original.key [publicMap key first later]) :
    Nonempty (InitialOutput row started [mappingValue key (entries key first later)]
      (mappingValue key (entries key (first + Word.ofNatModulo shape.right.resolution.rawValue) later))
      (mappingHeap ⟨[]⟩ key (entries key (first + Word.ofNatModulo shape.right.resolution.rawValue) later))) := by
  obtain ⟨chosen⟩ := selection row profile started
  let actual : WriteShape chosen.initial.header.function.source key := chosen.sourceEq.symm ▸ shape
  have certified := chosen.issued.support.certificates chosen.initial.header chosen.initial.start.selected.member
  obtain ⟨rawD,global,sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => write_plain chosen.initial.header actual certified sourceAt
    chosen.initial.header invocation ⟨[]⟩ first [(key.value,.word later)]
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [publicMap key first later] chosen.initial.header.types := by
    rw [write_input_types chosen.initial.header actual]
    exact map_types actual.keyNode (key.simple_valid actual.simple _) first later
  have rightEq : actual.right.resolution.rawValue = shape.right.resolution.rawValue :=
    cast_right chosen.sourceEq.symm shape
  refine ⟨{ toSelection := chosen
            plain := ?_
            forward := ?_ }⟩
  · simpa only [rightEq, entries] using plain
  · intro invocation
    have forward := chosen.initial.forward_data_output_plain types (map_meanings key first later) (plain invocation)
    simpa only [rightEq, entries] using forward

end Tests.SourceCoreSelectedGeneralKey
