import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterCertificates

/-! The named compiler installs parameter cells before passing its raw body to
its indexed hook. Successful production compilation supplies both the body
certificate at the extended scope and the actual parameter-allocation tree.
No semantic body or parameter execution is a static premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
open Core Frontend SourceInference CompatibleNamedBody
open CompatibleEncoding (bind_ok)

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

/-- Extract the real parameter prefix and the body at the actual input scope.
The allocator equality identifies its registered layout/profile explicitly. -/
theorem of_accepted
    {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {locals : SourceCoreLocalPolymorphism.Catalog}
    {native : Option SourceCoreGeneralFunctions.CallableContext}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {named : SourceCoreGeneralFunctions.Function}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {readFuel fuel : Nat} {values : SourceCoreCompatibleValues.Context} {code : Expr}
    {layouts : SourceCoreAllocationLayouts.Prepared} {allocationGlobals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (agreement : NamedAgreement named function)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionConstructors.Ordinary function.source locals named.signature.key)
    (unique : NodeOccurrencesUnique function.source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) context)
    (readExpression : (representation.atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : (representation.atContext named.signature.key []).expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : (representation.atContext named.signature.key []).expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (bodyContext plan globals named) native).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (bodyContext plan globals named) native).lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression program (representation.atContext named.signature.key [])
        signatures locals parents own.assignments diagnostics (bodyContext plan globals named) native none none)
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator ancestry.layout.frame allocationGlobals
        (layouts.allocatorAt named.signature.key [] onError)))
    (hook : representation.rawNamedBody = SourceCoreCallableIndexedAncestry.namedBody ancestry)
    (syntaxTree : CompatibleStatements.Syntax function.source context function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native fuel named = .ok code) :
    ∃ body parameterCode output,
      Nonempty (Certificate readFuel values function.source context named.specialized.function.solvedRequirements
        (diagnostics.reasonAt named.signature.key) (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)))
        function.body function.resultType named.signature.resultType
        (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
          diagnostics (bodyContext plan globals named) native) fuel own.fellThroughReason own.table.escapedReason body) ∧
      SourceCoreSourceCells.bindParameters
        (SourceCoreCallableIndexedAllocationFrames.allocator ancestry.layout.frame allocationGlobals
          (layouts.allocatorAt named.signature.key [] onError)) function.source [] named.inputs
        named.signature.resultType SourceCoreFunctions.argumentProjection body = .ok parameterCode ∧
      CallableIndexedParameterCertificates.Tree layouts named.signature.key [] ancestry.layout.frame allocationGlobals onError
        function.source named.inputs.length named.signature.resultType body [] 0 named.inputs parameterCode ∧
      SourceCoreCallableIndexedAncestry.namedBody ancestry named parameterCode = .ok output ∧
      code = .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output := by
  unfold SourceCoreGeneralFunctions.compileClosureWithRepresentation at accepted
  simp only [parentReceipt, Except.mapError, diagnosticReceipt, bind, Except.bind, pure, Except.pure] at accepted
  rw [← agreement.source, agreement.roots] at accepted
  have roots := roots_map function.body
  simp only [pure, Except.pure, List.mapM_map, Function.comp_def] at roots
  simp only [List.mapM_map, Function.comp_def] at accepted
  rw [roots] at accepted
  simp only [SourceCoreGeneralFunctions.bodyLowererWithRepresentation] at accepted
  cases bodyResult : SourceCoreLoops.lowerStatementsWithPolicy
      (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
        diagnostics (bodyContext plan globals named) native) fuel function.source
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) function.body named.signature.resultType
        (diagnostics.reasonAt named.signature.key) own.fellThroughReason own.table.escapedReason with
  | error error =>
    simp only [bodyPolicy, bodyContext] at bodyResult
    rw [bodyResult] at accepted
    cases accepted
  | ok body =>
    have certificate := CompatibleNamedBody.of_contextual ordinary unique closed residual declarations readExpression
      lowerRead leafLowerer readStatement lowerExpression syntaxTree projection bodyResult
    simp only [bodyPolicy, bodyContext] at bodyResult
    rw [bodyResult] at accepted
    rw [allocator] at accepted
    cases prefixResult : SourceCoreSourceCells.bindParameters
        (SourceCoreCallableIndexedAllocationFrames.allocator ancestry.layout.frame allocationGlobals
          (layouts.allocatorAt named.signature.key [] onError)) function.source [] named.inputs
        named.signature.resultType SourceCoreFunctions.argumentProjection body with
    | error error => simp [prefixResult] at accepted
    | ok parameterCode =>
      have tree := CallableIndexedParameterCertificates.of_accepted onError prefixResult
      simp only [prefixResult] at accepted
      obtain ⟨output, generated, same⟩ := bind_ok accepted
      simp only [SourceCoreGeneralFunctions.Representation.atContext, hook] at generated
      have hookAccepted : SourceCoreCallableIndexedAncestry.namedBody ancestry named parameterCode = .ok output := by
        cases result : SourceCoreCallableIndexedAncestry.namedBody ancestry named parameterCode with
        | error error => simp [result] at generated
        | ok actual => simp only [result, Except.ok.injEq] at generated; cases generated; rfl
      exact ⟨body, parameterCode, output, certificate, prefixResult, tree, hookAccepted, Except.ok.inj same.symm⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
