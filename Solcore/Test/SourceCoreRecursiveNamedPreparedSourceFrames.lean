import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The source invocation frame is constructed from actual pass receipts,
independent validity and the ordinary declaration dictionary condition. The
audit replays the actual closure compiler and inspects each full source view. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedSourceFrames
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedSpecializationBodyFacts RecursiveNamedPreparedSourceFrames

section Formal
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Core.Expr} {program : CheckedProgram}
  {representation : SourceCoreGeneralFunctions.Representation}
  {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
  {specialized : SourceSpecialization.SpecializedFunction}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)

include compiled

theorem compiled_source_roots :
    Dynamic.StatementRoots named.specialized.function.typedBody.roots compiled.statements := compiled_roots compiled

theorem prepared_source_agreement
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) := agreement inputs compiled

theorem actual_canonical_frame
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = []) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  canonical_frame signatureMember genericMember accepted valid closed compiled

theorem actual_retained_frame
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = []) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  retained_frame signatureMember genericMember accepted valid closed compiled

theorem actual_retained_bundle
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  retained_of_compilation signatureMember genericMember accepted valid closed inputs compiled

/-- A source body invocation is recovered from its independent trace using the
constructed frame; a prior SourceFrame is not an input. -/
theorem independent_body_trace
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = [])
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    {outcome : Dynamic.ExpressionOutcome}
    (extended : MonoBindersExtend named.specialized.function.typedBody.owner
      (bodyInstance program named.specialized).context named.specialized.function.typedBody.inputs types context)
    (allocated : Dynamic.BindersAllocate [] before named.specialized.function.typedBody.inputs arguments environment bound)
    (trace : FunctionCallBody.Trace (Program.ofChecked program) (view program named compiled.statements)
      context environment bound outcome after) :
    NamedCalls.BodyOutcome (Program.ofChecked program) (bodyInstance program named.specialized) []
      before arguments outcome after :=
  (retained_frame signatureMember genericMember accepted valid closed compiled).body_of_trace extended allocated trace
end Formal

theorem ordinary_empty_dictionary {program : CheckedProgram} {named : SourceCoreGeneralFunctions.Function}
    (closed : named.specialized.assumptions = []) :
    Dynamic.EvidenceEnvironment.Covers (bodyInstance program named.specialized).context [] := empty_covers closed

theorem expression_root_rejected (id : ExpressionId) (rest : List NodeId) (statements : List StatementId) :
    (NodeId.expression id :: rest).mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)) ≠ .ok statements := by
  simp [List.mapM_cons, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem view_entry_fields (program : CheckedProgram) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) :
    (view program named statements).captured = [] ∧ (view program named statements).evidence = [] ∧
      (view program named statements).context.residualTypeVariables = true := ⟨rfl, rfl, rfl⟩

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function local<T>(value: T) returns (T) { let copied = value; return copied; }",
  "function empty() {}",
  "function terminal(flag: Bool) returns (Word) { if (flag) { return 3; } else { return 4; } return 5; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function localRoot() returns (Word) { return local(11); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named prepared source frames" content
    ["wordRoot", "boolRoot", "localRoot", "empty", "terminal"]
  let representation := SourceCoreCompatibleFunctions.representation
    (.initial compiled.compatible.checked) compiled.compilationFuel
  let rawDiagnostics ← match compiled.indexed.base.diagnostics with
    | some value => pure value.program
    | none => throw (IO.userError "prepared source frames diagnostics missing")
  let diagnostics := match compiled.indexed.base.callableContext with
    | none => rawDiagnostics
    | some native => {rawDiagnostics with rootTable := native.diagnostics.rootTable}
  let mut rows := 0
  let mut emptyRows := 0
  let mut genericRows := 0
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let actual ← get "source frames actual input preparation"
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation compiled.sourceProgram representation named.specialized)
    require (reprStr actual == reprStr named) "source frames actual full prepared row changed"
    let code ← get "source frames actual closure compilation"
      (SourceCoreGeneralFunctions.compileClosureWithRepresentation compiled.indexed.base.sourceProgram
        (CallableIndexedNamedGeneration.representation compiled.indexed) compiled.indexed.base.sourceProgram.signatures
        compiled.indexed.base.plan compiled.indexed.base.globals diagnostics compiled.indexed.base.locals
        compiled.indexed.base.callableContext compiled.indexed.fuel named)
    require (compiled.indexed.secondPass.closures[slot]? == some code)
      "source frames real second pass/slot changed"
    let statements ← get "source frames actual root traversal"
      (named.specialized.function.typedBody.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let closure := view compiled.sourceProgram named statements
    require (reprStr closure.source == reprStr named.specialized.function.typedBody &&
      closure.source.roots == statements.map NodeId.statement)
      "source frames full source/root row changed"
    require (reprStr closure.parameters == reprStr (named.inputs.map Prod.fst) &&
      closure.resultType == named.specialized.function.inferredBodyType)
      "source frames raw ordered parameters/result changed"
    require (closure.captured.isEmpty && closure.evidence.isEmpty && named.specialized.assumptions.isEmpty)
      "source frames ordinary source entry dictionary/capture changed"
    require (reprStr closure.context == reprStr (bodyInstance compiled.sourceProgram named.specialized).context &&
      closure.context.residualTypeVariables && closure.context.typeParameters.isEmpty)
      "source frames full original context/ledger flags changed"
    let retained := CallableNamedCanonicalOrder.retainedInstantiation named.specialized
    require (retained.parameterSubstitution == named.specialized.parameterSubstitution.reverse &&
      retained.type == named.specialized.function.type && retained.parameterComptime == closure.parameters.map (·.comptime))
      "source frames full retained substitution/flags changed"
    if statements.isEmpty then emptyRows := emptyRows + 1
    if !named.specialized.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    rows := rows + 1
  require (rows == 8 && emptyRows == 1 && genericRows == 3)
    s!"source frames actual fixture coverage changed {rows}/{emptyRows}/{genericRows}"
  IO.println "named prepared source frames: actual roots/input preparation/closure compilation, complete ordinary canonical and retained views GREEN"

end Tests.SourceCoreRecursiveNamedPreparedSourceFrames
