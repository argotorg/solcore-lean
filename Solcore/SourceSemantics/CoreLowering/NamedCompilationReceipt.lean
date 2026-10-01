import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCompilation

/-! A static receipt for the actual named-function compiler. The body
certificate is an arbitrary proposition obtained from the accepted body
lowering. It has no semantic fields. The receipt retains the real parameter
prefix and named hook equations so concrete syntax certificates can share the
compiler decomposition without assuming body preservation or reflection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCompilationReceipt
open Core Frontend SourceInference
open CompatibleNamedBody (bodyContext bodyPolicy)
open CompatibleEncoding (bind_ok)

/-- The compiler's exact body request, after all parameter binders enter scope. -/
def bodyRequest (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (signatures : ProgramSignatures) (plan : SourceSpecializationWorklist.Plan)
    (globals : List SourceCoreCalls.Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (locals : SourceCoreLocalPolymorphism.Catalog) (native : Option SourceCoreGeneralFunctions.CallableContext)
    (parents : List SourceCoreLocalEvidence.Prepared) (own : SourceCoreProgramFaultSites.Function)
    (named : SourceCoreGeneralFunctions.Function) (statements : List StatementId) (fuel : Nat) :
    Except SourceCoreBasic.Error Expr :=
  SourceCoreLoops.lowerStatementsWithPolicy
    (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
      diagnostics (bodyContext plan globals named) native)
    fuel named.specialized.function.typedBody
    (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) statements named.signature.resultType
    (diagnostics.reasonAt named.signature.key) own.fellThroughReason own.table.escapedReason

/-- All fields are static compiler receipts. In particular, `certified` is a
proposition about the emitted body, with no runtime meaning supplied here. -/
structure Receipt (program : CheckedProgram) (representation : SourceCoreGeneralFunctions.Representation)
    (signatures : ProgramSignatures) (plan : SourceSpecializationWorklist.Plan)
    (globals : List SourceCoreCalls.Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (locals : SourceCoreLocalPolymorphism.Catalog) (native : Option SourceCoreGeneralFunctions.CallableContext)
    (parents : List SourceCoreLocalEvidence.Prepared) (own : SourceCoreProgramFaultSites.Function)
    (named : SourceCoreGeneralFunctions.Function) (statements : List StatementId) (fuel : Nat)
    (allocate : SourceCoreSourceCells.Allocator) (bodyCertificate : Expr → Prop) (code : Expr) where private mk ::
  body : Expr
  parameterCode : Expr
  output : Expr
  accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
    diagnostics locals native fuel named = .ok code
  parentsAccepted : SourceCoreStageCodebook.prepareContexts program plan
    (locals.bindings.flatMap (·.instances)) = .ok parents
  diagnosticsAccepted : diagnostics.base.find? named.signature.key = some own
  roots : named.specialized.function.typedBody.roots = statements.map NodeId.statement
  allocator : (representation.atContext named.signature.key []).expressions.sourceCells = some allocate
  bodyAccepted : bodyRequest program representation signatures plan globals diagnostics locals native parents own
    named statements fuel = .ok body
  certified : bodyCertificate body
  parametersAccepted : SourceCoreSourceCells.bindParameters allocate named.specialized.function.typedBody [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection body = .ok parameterCode
  hookAccepted : representation.rawNamedBody named parameterCode = .ok output
  emitted : code = .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output

private theorem roots_map (statements : List StatementId) :
    (statements.map NodeId.statement).mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id
      | .expression id => throw (.expectedStatementRoot id)) = .ok statements := by
  induction statements with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih]
    rfl

/-- An actual compiler success yields the body certificate by the supplied
static extraction theorem. No source/Core execution or semantic body IH is a
premise. `extract` will be instantiated with a closed syntax-tree extraction. -/
theorem of_accepted
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {locals : SourceCoreLocalPolymorphism.Catalog} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {named : SourceCoreGeneralFunctions.Function} {statements : List StatementId} {fuel : Nat}
    {allocate : SourceCoreSourceCells.Allocator} {bodyCertificate : Expr → Prop} {code : Expr}
    (roots : named.specialized.function.typedBody.roots = statements.map NodeId.statement)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan
      (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells = some allocate)
    (extract : ∀ body, bodyRequest program representation signatures plan globals diagnostics locals native parents own
      named statements fuel = .ok body → bodyCertificate body)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native fuel named = .ok code) :
    Nonempty (Receipt program representation signatures plan globals diagnostics locals native parents own
      named statements fuel allocate bodyCertificate code) := by
  have compiled := accepted
  unfold SourceCoreGeneralFunctions.compileClosureWithRepresentation at accepted
  simp only [parentReceipt, Except.mapError, diagnosticReceipt, bind, Except.bind, pure, Except.pure] at accepted
  rw [roots] at accepted
  have mapped := roots_map statements
  simp only [pure, Except.pure, List.mapM_map, Function.comp_def] at mapped
  simp only [List.mapM_map, Function.comp_def] at accepted
  rw [mapped] at accepted
  simp only [SourceCoreGeneralFunctions.bodyLowererWithRepresentation] at accepted
  cases bodyResult : bodyRequest program representation signatures plan globals diagnostics locals native parents own
      named statements fuel with
  | error error =>
    simp only [bodyRequest, bodyPolicy, bodyContext] at bodyResult
    rw [bodyResult] at accepted
    cases accepted
  | ok body =>
    have certified := extract body bodyResult
    have lowering := bodyResult
    simp only [bodyRequest, bodyPolicy, bodyContext] at lowering
    rw [lowering, allocator] at accepted
    cases prefixResult : SourceCoreSourceCells.bindParameters allocate named.specialized.function.typedBody [] named.inputs
        named.signature.resultType SourceCoreFunctions.argumentProjection body with
    | error error => simp [prefixResult] at accepted
    | ok parameterCode =>
      simp only [prefixResult] at accepted
      obtain ⟨output, generated, same⟩ := bind_ok accepted
      simp only [SourceCoreGeneralFunctions.Representation.atContext] at generated
      have hookAccepted : representation.rawNamedBody named parameterCode = .ok output := by
        cases result : representation.rawNamedBody named parameterCode with
        | error error => simp [result] at generated
        | ok actual => simp only [result, Except.ok.injEq] at generated; cases generated; rfl
      exact ⟨⟨body, parameterCode, output, compiled, parentReceipt, diagnosticReceipt, roots, allocator,
        bodyResult, certified, prefixResult, hookAccepted, Except.ok.inj same.symm⟩⟩

end Solcore.SourceSemantics.CoreLowering.NamedCompilationReceipt
