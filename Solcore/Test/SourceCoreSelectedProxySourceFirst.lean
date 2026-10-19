import Solcore.Test.SourceCoreSelectedProxyFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicInitialData

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProxy
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

/-- The original @T expression produces a proxy with exactly its raw inner
identity, before any native execution is observed. -/
theorem literal_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (inner : TypeSystem.Ty) (shape : LiteralShape row.original.function.typedBody inner)
    (started : Started fixture row.original.key []) :
    Nonempty (InitialOutput row started [] (.proxy inner) ⟨[]⟩) := by
  obtain ⟨chosen⟩ := selection row profile started
  have actual : LiteralShape chosen.initial.header.function.source inner := by
    rw [chosen.sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => literal_plain chosen.initial.header actual sourceAt
    chosen.initial.header invocation ⟨[]⟩
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [] chosen.initial.header.types := by
    rw [literal_types chosen.initial.header actual]; exact .nil
  exact ⟨{
    toSelection := chosen
    plain := plain
    forward := fun invocation => chosen.initial.forward_data_output_plain types .nil (plain invocation) }⟩

/-- A fresh proxy public input has an independent raw-typing/meaning receipt;
the actual initial metadata encoder and whole-output theorem preserve it. -/
theorem echo_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (inner : TypeSystem.Ty) (shape : EchoShape row.original.function.typedBody inner)
    (started : Started fixture row.original.key [.proxy inner]) :
    Nonempty (InitialOutput row started [.proxy inner] (.proxy inner) (echoHeap ⟨[]⟩ inner)) := by
  obtain ⟨chosen⟩ := selection row profile started
  have actual : EchoShape chosen.initial.header.function.source inner := by
    rw [chosen.sourceEq]; exact shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => echo_plain chosen.initial.header actual sourceAt
    chosen.initial.header invocation ⟨[]⟩
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [.proxy inner] chosen.initial.header.types := by
    rw [echo_types chosen.initial.header actual]
    exact .cons ⟨.proxy inner, by simp [SourceCoreIndexedSession.DataInput.publicValue], .proxy inner⟩ .nil
  have means : RecursiveNamedPublicDataInputs.Meanings [.proxy inner] [.proxy inner] :=
    .cons ⟨.proxy inner, by simp [SourceCoreIndexedSession.DataInput.publicValue], .proxy inner⟩ .nil
  exact ⟨{
    toSelection := chosen
    plain := plain
    forward := fun invocation => chosen.initial.forward_data_output_plain types means (plain invocation) }⟩

end Tests.SourceCoreSelectedProxy
