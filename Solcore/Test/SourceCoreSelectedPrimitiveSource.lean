import Solcore.Test.SourceCoreSelectedPrimitiveFixture

/-! The ordinary complement trace is built from the original checked nodes and
one fresh input cell. No completed public run or reflected trace is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedPrimitiveSource
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreSelectedPrimitiveFixture
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (PlainValue SourceCall)

structure ComplementShape {fixture : Fixture} (row : Row fixture) where
  binder : TypedBinder
  read : ExpressionNode
  unary : ExpressionNode
  statement : StatementNode
  inputs : row.row.function.typedBody.inputs = [binder]
  scheme : binder.scheme = .mono .word
  roots : row.row.function.typedBody.roots = [.statement statement.id]
  readFound : row.row.function.typedBody.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  unaryFound : row.row.function.typedBody.lookupExpression? unary.id = some unary
  unaryForm : unary.form = .unary .bitNot read.id
  unaryRequirements : unary.requirements = []
  unaryCoercions : unary.coercions = []
  found : row.row.function.typedBody.lookupStatement? statement.id = some statement
  form : statement.form = .returnStmt (some unary.id)
  result : row.row.function.inferredBodyType = .word
  native : row.global.resultType = .word

def observeComplement {fixture : Fixture} (row : Row fixture) : IO (ComplementShape row) := do
  let source := row.row.function.typedBody
  match inputs : source.inputs, roots : source.roots with
  | [binder], [.statement statementId] =>
    match found : source.lookupStatement? statementId with
    | none => throw (IO.userError "primitive return node missing")
    | some statement =>
      match form : statement.form with
      | .returnStmt (some unaryId) =>
        match unaryFound : source.lookupExpression? unaryId with
        | none => throw (IO.userError "primitive operator node missing")
        | some unary =>
          match unaryForm : unary.form with
          | .unary .bitNot readId =>
            match readFound : source.lookupExpression? readId with
            | none => throw (IO.userError "primitive operand missing")
            | some read =>
              let ⟨scheme⟩ ← observed (binder.scheme = .mono .word) "primitive binder scheme"
              let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "primitive read form"
              let ⟨readRequirements⟩ ← observed (read.requirements = []) "primitive read requirements"
              let ⟨readCoercions⟩ ← observed (read.coercions = []) "primitive read coercions"
              let ⟨unaryRequirements⟩ ← observed (unary.requirements = []) "primitive operator requirements"
              let ⟨unaryCoercions⟩ ← observed (unary.coercions = []) "primitive operator coercions"
              let ⟨result⟩ ← observed (row.row.function.inferredBodyType = .word) "primitive result"
              let ⟨native⟩ ← observed (row.global.resultType = .word) "primitive native result"
              have readIdEq := (lookupExpression?_sound readFound).2
              have unaryIdEq := (lookupExpression?_sound unaryFound).2
              have statementIdEq := (lookupStatement?_sound found).2
              return ⟨binder, read, unary, statement, inputs, scheme,
                by simpa only [statementIdEq] using roots,
                by simpa only [readIdEq] using readFound, readForm, readRequirements, readCoercions,
                by simpa only [unaryIdEq] using unaryFound,
                by simpa only [readIdEq] using unaryForm, unaryRequirements, unaryCoercions,
                by simpa only [statementIdEq] using found,
                by simpa only [unaryIdEq] using form, result, native⟩
          | _ => throw (IO.userError "primitive complement form changed")
      | _ => throw (IO.userError "primitive return form changed")
  | _, _ => throw (IO.userError "primitive input/body shape changed")

def appendWord (before : Dynamic.Heap) (value : Word) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .word, value := some (.word value)}]⟩

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head rest ih =>
    cases right with
    | nil => simp_all
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨same, tails⟩ := same
      cases same
      simp only [ih tails]

variable {fixture : Fixture} {row : Row fixture}
  (shape : ComplementShape row)
  (header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
  (same : header.named.specialized = row.row)

include shape same in
theorem complement_plain
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (value : Word) :
    PlainValue header header invocation before [.word value] (.word value.bitNot) (appendWord before value) := by
  have source : header.function.source = row.row.function.typedBody := by rw [header.agreement.source, same]
  have parameters : header.function.parameters = [shape.binder] := by
    rw [header.parameters, ← header.inputs, source, shape.inputs]
  have statements : header.function.body = [shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (by rw [source, shape.roots]; rfl))
  have allocated : Dynamic.Heap.Allocates before shape.binder.scheme.body (some (.word value))
      ⟨before.cells.length⟩ (appendWord before value) := by rw [shape.scheme]; exact .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word value]
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value) := by
    rw [parameters]; exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value)
      shape.read.id (.word value) (appendWord before value) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound (source.symm ▸ shape.readFound))
    · rw [shape.readForm]
      exact .local (by rw [shape.readRequirements, shape.readCoercions]; rfl) .head allocated.reads_new rfl rfl
    · rw [shape.readCoercions]; exact .nil
  have unary : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value)
      shape.unary.id (.word value.bitNot) (appendWord before value) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound (source.symm ▸ shape.unaryFound))
    · rw [shape.unaryForm]
      exact .unary (owned := []) (by rw [shape.unaryRequirements, shape.unaryCoercions]; rfl)
        read (.primitive (.wordBitNot value))
    · rw [shape.unaryCoercions]; exact .nil
  have executed : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value)
      header.function.body header.context (.returned (.word value.bitNot)) (appendWord before value) := by
    rw [statements]
    have found := lookupStatement?_sound (source.symm ▸ shape.found)
    exact .singleton found (by rw [shape.form]; intro expression impossible; cases impossible)
      (.returnValue found shape.form unary)
  have body := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned executed)
  cases body with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

structure Conclusion (issued : Profiled fixture.recipe)
    {value : Word} (started : Started fixture row.row.key [.word value])
    (invocation : Staging.Recursive.Scope) where
  initial : Initial issued.toIssued started.call
  plain : PlainValue initial.header initial.header invocation ⟨[]⟩ [.word value]
    (.word value.bitNot) (appendWord ⟨[]⟩ value)
  forward :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word value] (.value (.word value.bitNot))
      (appendWord ⟨[]⟩ value) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word value.bitNot) started.call
        (appendWord ⟨[]⟩ value)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word value]

include shape in
/-- Checking, the executable profile, finite source shape and a startup receipt
produce the independent ordinary trace and the closed sufficient-fuel theorem. -/
theorem from_source (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {value : Word} (started : Started fixture row.row.key [.word value])
    (invocation : Staging.Recursive.Scope) :
    ∃ issued : Profiled fixture.recipe, Nonempty (Conclusion issued started invocation) := by
  obtain ⟨issued, initial, same, signature⟩ := Tests.SourceCoreSelectedPrimitiveFixture.initial profile row started
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := complement_plain shape initial.header same sourceAt invocation ⟨[]⟩ value
  have simple : ∀ v ∈ ([.word value] : List SourceCorePublicValues.Value), SourceCoreIndexedSession.SimplePublic v := by
    intro v member; cases List.mem_singleton.mp member; exact .word value
  have types : initial.header.types = [.word] := by
    have eq := Dynamic.MonoBindersExtend.bodyTypes_eq initial.header.extended
    have parameters : initial.header.function.parameters = [shape.binder] := by
      rw [initial.header.parameters, ← initial.header.inputs, initial.header.agreement.source, same, shape.inputs]
    simpa only [parameters, List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using eq.symm
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word value] initial.header.types := by
    rw [types]
    exact .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word value] [.word value] :=
    .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil
  have raw : initial.header.function.resultType = .word := by rw [initial.header.agreement.result, same, shape.result]
  have native : initial.header.output = .word := by rw [← initial.header.resultType, signature, shape.native]
  exact ⟨issued, ⟨⟨initial, plain, SelectedCompilationStageClosedInitialForward.scalar issued started.call
    initial simple inputTypes meanings (.word value.bitNot) raw native plain⟩⟩⟩

end Tests.SourceCoreSelectedPrimitiveSource
