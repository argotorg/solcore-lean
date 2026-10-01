import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyIndexed

/-! Extraction from the actual zero-parameter named-function compiler. The
source/diagnostic/contextual-parent receipts are static preflight facts. The
compiled body tree and accepted indexed named hook are obtained from compiler
success, rather than assumed child trees or semantic body hypotheses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

def bodyContext (plan : SourceSpecializationWorklist.Plan) (globals : List SourceCoreCalls.Signature)
    (named : SourceCoreGeneralFunctions.Function) : SourceCoreFunctions.Context := {
  plan, globals, owner := named.signature.key, administrativePrefix := 1
  solvedRequirements := named.specialized.function.solvedRequirements
  internalReason := Word.zero
}

def bodyPolicy (representation : SourceCoreGeneralFunctions.Representation)
    (program : CheckedProgram) (signatures : ProgramSignatures)
    (locals : SourceCoreLocalPolymorphism.Catalog) (parents : List SourceCoreLocalEvidence.Prepared)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (context : SourceCoreFunctions.Context) (native : Option SourceCoreGeneralFunctions.CallableContext) : SourceCoreLoops.Policy := {
  representation.loopsWithSourceCells representation.expressions.sourceCells context.solvedRequirements assignments diagnostics context.owner
    (SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments diagnostics
      context native none none) with
  sourceCells := representation.expressions.sourceCells
  lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation locals context.owner []
}

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

/-- The source attribution is stated independently of emitted Core shape. -/
structure NamedAgreement (named : SourceCoreGeneralFunctions.Function) (function : Dynamic.Closure) : Prop where
  source : function.source = named.specialized.function.typedBody
  roots : function.source.roots = function.body.map NodeId.statement
  parameters : function.parameters = named.inputs.map Prod.fst
  result : function.resultType = named.specialized.function.inferredBodyType

/-- For zero parameters, compiler success yields the real body certificate and
the actual frame-installation hook equation. No parameter prefix is erased. -/
theorem zero_of_accepted
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
    (agreement : NamedAgreement named function) (parameters : named.inputs = [])
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionConstructors.Ordinary function.source locals named.signature.key)
    (unique : NodeOccurrencesUnique function.source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source [] context)
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
    (hook : representation.rawNamedBody = SourceCoreCallableIndexedAncestry.namedBody ancestry)
    (syntaxTree : CompatibleStatements.Syntax function.source context function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native fuel named = .ok code) :
    ∃ body output,
      Nonempty (Certificate readFuel values function.source context named.specialized.function.solvedRequirements
        (diagnostics.reasonAt named.signature.key) [] function.body function.resultType named.signature.resultType
        (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
          diagnostics (bodyContext plan globals named) native) fuel own.fellThroughReason own.table.escapedReason body) ∧
      SourceCoreCallableIndexedAncestry.namedBody ancestry named body = .ok output ∧
      code = .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output := by
  unfold SourceCoreGeneralFunctions.compileClosureWithRepresentation at accepted
  simp only [parentReceipt, Except.mapError, diagnosticReceipt, bind, Except.bind, pure, Except.pure] at accepted
  rw [← agreement.source, agreement.roots] at accepted
  have roots := roots_map function.body
  simp only [pure, Except.pure, List.mapM_map, Function.comp_def] at roots
  simp only [List.mapM_map, Function.comp_def] at accepted
  rw [roots] at accepted
  simp only [parameters, List.reverse_nil, List.map_nil,
    SourceCoreGeneralFunctions.bodyLowererWithRepresentation] at accepted
  cases result : SourceCoreLoops.lowerStatementsWithPolicy
      (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
        diagnostics (bodyContext plan globals named) native) fuel function.source [] function.body named.signature.resultType
        (diagnostics.reasonAt named.signature.key) own.fellThroughReason own.table.escapedReason with
  | error error =>
    simp only [bodyPolicy, bodyContext] at result
    rw [result] at accepted
    cases accepted
  | ok body =>
    have certificate := of_contextual ordinary unique closed residual declarations readExpression lowerRead leafLowerer
      readStatement lowerExpression syntaxTree projection result
    simp only [bodyPolicy, bodyContext] at result
    rw [result] at accepted
    cases sourceCells : representation.allocatorAt named.signature.key [] <;>
      simp [SourceCoreGeneralFunctions.Representation.atContext, sourceCells,
        SourceCoreFunctions.bindParameters, SourceCoreSourceCells.bindParameters,
        hook, pure, Except.pure] at accepted
    all_goals
      obtain ⟨output, generated, same⟩ := bind_ok accepted
      have hookAccepted : SourceCoreCallableIndexedAncestry.namedBody ancestry named body = .ok output := by
        cases result : SourceCoreCallableIndexedAncestry.namedBody ancestry named body with
        | error error => simp [result] at generated
        | ok actual => simp only [result, Except.ok.injEq] at generated; cases generated; rfl
      exact ⟨body, output, certificate, hookAccepted, Except.ok.inj same.symm⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
