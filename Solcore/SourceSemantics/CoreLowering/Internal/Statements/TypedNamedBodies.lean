import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters

/-!
# Typed named bodies

Certificates and meaning of typed named bodies and their parameters.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCompilationReceipt
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyCertificates
/-! Static receipts for the ordinary mixed lexical named-body fragment. A receipt
retains the actual production traversal equation and its extracted statement
tree at its initial source context. It contains no body execution or semantic induction
hypothesis. Context/evidence validity remains a separate static obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody
open Core Frontend SourceInference

structure Certificate (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (policy : SourceCoreLoops.Policy) (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    type reasonAt fellThrough escaped = .ok code
  flow : Expr
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : TypedStatementMixed.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope
    statements expected type flow

/-- Extract the body tree from the actual contextual compiler. Every remaining
premise concerns source syntax, typing, context, or a production policy field. -/
theorem of_contextual
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy}
    (ordinary : CompatibleExpressionTyped.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : TypedStatementMixed.Syntax source context statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    Nonempty (Certificate layouts owner active frame globals onError readFuel values source context compilation.solvedRequirements reasonAt scope
      statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, emitted, tree⟩ := TypedStatementMixed.tree_of_contextual_body ordinary unique closed residual sourceSignatures
    declarations readExpression lowerRead leafLowerer readStatement representationBinder lowerBinder sourceCells lowerExpression syntaxTree projection accepted
  exact ⟨⟨accepted, flow, emitted, tree⟩⟩

/-- Instantiate the generic named compiler decomposition with the concrete
closed mixed lexical typed-statement tree, at the actual scope after parameter installation.
All context/evidence/ordinary obligations are explicit static hypotheses. -/
theorem compilation_of_accepted
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {allocationGlobals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {locals : SourceCoreLocalPolymorphism.Catalog}
    {native : Option SourceCoreGeneralFunctions.CallableContext}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {named : SourceCoreGeneralFunctions.Function}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {readFuel fuel : Nat} {values : SourceCoreCompatibleValues.Context} {code : Expr}
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan
      (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionTyped.Ordinary function.source locals named.signature.key)
    (unique : NodeOccurrencesUnique function.source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readExpression : (representation.atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : (representation.atContext named.signature.key []).expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : (representation.atContext named.signature.key []).expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native).lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression program (representation.atContext named.signature.key [])
        signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native none none)
    (representationBinder : (representation.atContext named.signature.key []).expressions.lowerBinder =
      SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native).lowerBinder =
      SourceCoreGeneralFunctions.contextualBinder (representation.atContext named.signature.key []) locals named.signature.key [])
    (sourceCells : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native).sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)))
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)))
    (syntaxTree : TypedStatementMixed.Syntax function.source context function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native fuel named = .ok code) :
    Nonempty (NamedCompilationReceipt.Receipt program representation signatures plan globals diagnostics locals native parents own
      named function.body fuel
      (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)) (fun body => Nonempty (Certificate layouts owner active frame allocationGlobals onError readFuel values function.source context
        named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType
        named.signature.resultType (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key [])
          program signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native)
        fuel own.fellThroughReason own.table.escapedReason body)) code) := by
  apply NamedCompilationReceipt.of_accepted (agreement.source ▸ agreement.roots) parentReceipt diagnosticReceipt allocator ?_ accepted
  intro body lowered
  change SourceCoreLoops.lowerStatementsWithPolicy _ _ _ _ _ _ _ _ _ = .ok body at lowered
  rw [← agreement.source] at lowered
  exact of_contextual ordinary unique closed residual declarations sourceSignatures readExpression lowerRead leafLowerer
    readStatement representationBinder lowerBinder sourceCells lowerExpression syntaxTree projection lowered

end Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedNamedBodyCertificates
/-! Static receipts for the ordinary fixed-scope named-body fragment. A receipt
retains the actual production traversal equation and its extracted statement
tree at one source context. It contains no body execution or semantic induction
hypothesis. Context/evidence validity remains a separate static obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedNamedBody
open Core Frontend SourceInference

structure Certificate (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (policy : SourceCoreLoops.Policy) (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    type reasonAt fellThrough escaped = .ok code
  flow : Expr
  emitted : code = TypedStatements.finish type flow fellThrough escaped
  tree : TypedStatements.Tree readFuel values source context solved reasonAt scope
    statements expected type flow

/-- Extract the body tree from the actual contextual compiler. Every remaining
premise concerns source syntax, typing, context, or a production policy field. -/
theorem of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy}
    (ordinary : CompatibleExpressionTyped.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : TypedStatements.Syntax source context statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    Nonempty (Certificate readFuel values source context compilation.solvedRequirements reasonAt scope
      statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, emitted, tree⟩ := TypedStatements.tree_of_contextual_body ordinary unique closed residual
    declarations sourceSignatures readExpression lowerRead leafLowerer readStatement lowerExpression syntaxTree projection accepted
  exact ⟨⟨accepted, flow, emitted, tree⟩⟩

/-- Instantiate the generic named compiler decomposition with the concrete
closed typed-statement tree, at the actual scope after parameter installation.
All context/evidence/ordinary obligations are explicit static hypotheses. -/
theorem compilation_of_accepted
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {locals : SourceCoreLocalPolymorphism.Catalog}
    {native : Option SourceCoreGeneralFunctions.CallableContext}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {named : SourceCoreGeneralFunctions.Function}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {readFuel fuel : Nat} {values : SourceCoreCompatibleValues.Context} {code : Expr}
    {allocate : SourceCoreSourceCells.Allocator}
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan
      (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionTyped.Ordinary function.source locals named.signature.key)
    (unique : NodeOccurrencesUnique function.source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readExpression : (representation.atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : (representation.atContext named.signature.key []).expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : (representation.atContext named.signature.key []).expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native).lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression program (representation.atContext named.signature.key [])
        signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native none none)
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells = some allocate)
    (syntaxTree : TypedStatements.Syntax function.source context function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native fuel named = .ok code) :
    Nonempty (NamedCompilationReceipt.Receipt program representation signatures plan globals diagnostics locals native parents own
      named function.body fuel allocate (fun body => Nonempty (Certificate readFuel values function.source context
        named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType
        named.signature.resultType (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key [])
          program signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) native)
        fuel own.fellThroughReason own.table.escapedReason body)) code) := by
  apply NamedCompilationReceipt.of_accepted (agreement.source ▸ agreement.roots) parentReceipt diagnosticReceipt allocator ?_ accepted
  intro body lowered
  change SourceCoreLoops.lowerStatementsWithPolicy _ _ _ _ _ _ _ _ _ = .ok body at lowered
  rw [← agreement.source] at lowered
  exact of_contextual ordinary unique closed residual declarations sourceSignatures readExpression lowerRead leafLowerer
    readStatement lowerExpression syntaxTree projection lowered

end Solcore.SourceSemantics.CoreLowering.TypedNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedNamedBodyMeaning
/-! The concrete typed-statement tree closes body meaning at its actual call
context and ambient definition table. Runtime environment typing is an explicit
entry fact. All expression children, including arbitrary scalar-key indices,
are discharged by the tree rather than a caller-provided semantic body IH. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleNamedBody (trace_control body_result)

/-- The fixed grammar cannot manufacture fault control through successful
source execution. Actual source faults retain their separate fault derivation. -/
theorem tree_control_not_fault {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : TypedStatements.Tree readFuel values source context solved reasonAt scope statements expected type flow)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : Dynamic.FunctionStatementsExecute program actualContext evidence source environment before
      statements finalContext (.fault reason) after) : False := by
  induction tree generalizing actualContext finalContext environment before after with
  | nil => cases executed
  | @returnUnit id node rest found form =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
  | @returnValue id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
  | tail found form expressionFound valueType value =>
    cases executed with
    | singleton contains notTail head =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
      subst_vars
      exact notTail _ form
  | @discard id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih =>
    have contains := lookupStatement?_sound found
    have notTailExpression : true = true → rest = [] → ∀ other, node.form ≠ .expression other false := by
      intro _ empty other impossible
      rw [form] at impossible
      cases impossible
      simp [empty] at notTail
    rcases ScalarStatementViews.cons_view true unique contains notTailExpression executed with
      ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨rfl, same, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact ih tail
    · obtain ⟨_, impossible, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases impossible

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension contextValid unique uninitialized missing in
theorem Certificate.preserves
    (certificate : Certificate readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨_, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨_, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    certificate.tree.body_preserves functions extension program function.evidence contextValid unique uninitialized missing
      fellThrough escaped environments heaps locals agrees actualTyped sourceTrace
  rw [← certificate.emitted] at evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, body_result represented exit,
    finalHeaps, maps, worlds, frame, metadata⟩

include extension contextValid unique uninitialized missing in
theorem Certificate.reflects
    (certificate : Certificate readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rw [certificate.emitted] at evaluated
  obtain ⟨control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    certificate.tree.body_reflects functions extension program function.evidence contextValid uninitialized missing
      fellThrough escaped environments heaps locals agrees actualTyped evaluated
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value := by
    generalize raw : function.resultType = expected at represented
    cases represented with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact .value .unit
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact .value payload
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (tree_control_not_fault certificate.tree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched⟩
  obtain ⟨outcome, trace, result⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩


end Solcore.SourceSemantics.CoreLowering.TypedNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyMeaning
/-! The concrete mixed tree closes body meaning at the actual call context and
ambient definitions. Its result retains the lexical context where execution
stopped. Initial environment typing is explicit; every child expression's
meaning, including nested scalar-key indices, is derived from the tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleNamedBody (trace_control body_result)

/-- The actual lexical stopping context is retained with the represented exit.
An initializer fault stops before its declaration enters the source context. -/
def ReachedExit (checked : SourceCoreCompatibleCatalog.Checked) (definitions : DataEnvironment)
    (mapping : LocationMap) (world : StoreTyping) (administrative : Core.Context)
    (program : Program) (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (environment : Dynamic.Environment)
    (before after : Dynamic.Heap) (outcome : Dynamic.ExpressionOutcome) : Prop :=
  ∃ (resultContext : SourceSemantics.Context) (control : Dynamic.ControlOutcome),
    Dynamic.FunctionStatementsExecuteOutcome program context function.evidence function.source
      environment before function.body resultContext control after ∧
    CompatibleNamedBody.Exit function.resultType control outcome ∧
    TypedStatementMixed.LexicalResult checked definitions mapping world administrative function.source.owner
      context scope environment resultContext after

/-- Successful source control through the ordinary binding spine cannot be a
fault. The initialized head can fault only through its separate fault relation. -/
theorem tree_control_not_fault
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : TypedStatementMixed.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type flow)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : Dynamic.FunctionStatementsExecute program actualContext evidence source environment before
      statements finalContext (.fault reason) after) : False := by
  induction tree generalizing actualContext finalContext environment before after with
  | body body => exact TypedNamedBody.tree_control_not_fault body unique executed
  | @uninitialized context nextContext scope id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨_, _, same, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases same
      exact ih tail
    · obtain ⟨_, _, same, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases same
  | @initialized context nextContext scope id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same
      exact ih tail
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include definitions registered extension contextValid unique uninitialized missing in
theorem Certificate.preserves
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.body_preserves functions definitions registered extension program function.evidence uninitialized missing
      contextValid fellThrough escaped unique environments heaps locals agrees actualTyped reference read unmapped sourceTrace
  rw [← certificate.emitted] at evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, body_result represented exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩⟩

include definitions registered extension contextValid unique uninitialized missing in
theorem Certificate.reflects
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  rw [certificate.emitted] at evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.body_reflects functions definitions registered extension program function.evidence uninitialized missing
      contextValid fellThrough escaped environments heaps locals agrees actualTyped reference read unmapped evaluated
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at represented
    cases represented with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (tree_control_not_fault certificate.tree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩⟩


end Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameterMeaning
/-! Parameter installation reaches the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
body correspondence comes from the extracted mixed lexical certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

structure Entry (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings actualContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type definitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) definitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

/-- Actual prefix receipts construct parameter allocation, the typed body
environment and the surviving context-reference slot. Its read and unmapped
status follow from allocation preservation. No final body facts are assumed. -/
theorem entry_of_accepted_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ entry : Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added : Environment, added.length = bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues nativeArguments :: canonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, agreement⟩ :=
    CallableIndexedParameterTyped.prefix_typed tree definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds inputs)
      (by simpa using reference) read unmapped
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length
      (DataPatternValues.packValues nativeArguments) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  have finalReference : finalLogical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : bindings.length + 1 + globals = added.length + (globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  exact ⟨⟨environment, heap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, preservation, GenericLexicalContext.binders_metadata allocated, lookups, finalTyped,
    finalReference, unchanged.trans read, finalUnmapped, agreement⟩, added, prefixLength, logicalEq⟩

/-- Legacy entry forgets only the actual ordered prefix witness. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body) := by
  obtain ⟨entry, _, _, _⟩ := entry_of_accepted_with_spine functions onError accepted parameters inputs extended definitions registered represented
    environments heaps initialLocals actualLayout actualTyped reference read unmapped
  exact ⟨entry⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
  (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}

include definitions registered extension contextValid unique uninitialized missing in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem Entry.preserves
    (entry : Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : TypedMixedNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    certificate.preserves functions extension definitions registered program contextValid unique uninitialized missing entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

include definitions registered extension contextValid unique uninitialized missing in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem Entry.reflects
    (entry : Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : TypedMixedNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    certificate.reflects functions extension definitions registered program contextValid unique uninitialized missing entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

end Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameterIndexed
/-! The actual named hook encloses the complete marked parameter prefix. Its
body certificate starts at the installed call context and retains its actual lexical stopping context. Native and
source parameter allocations precede that continuation, and the caller frame
and protected snapshots are restored after either represented body outcome. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters.Indexed
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (certificate : TypedMixedNamedBody.Certificate layouts owner active prepared.layout.frame allocationGlobals onError readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named (parameterCode.rename ξ) = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- A source allocation and its finite body trace execute the real full named
hook. Parameters are compared with the independently constructed allocation. -/
theorem preserves {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store code value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    entry.preserves functions extension definitions registered program contextValid unique uninitialized missing certificate trace
  rw [rename_prefix] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var actualReference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    emitted.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, by simpa only [sameEnvironment, sameHeap] using reached⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- Completed actual native execution constructs both source parameter
allocation and the independent body trace from the installed call context with its actual lexical stopping context. -/
theorem reflects {value : Value} {finalStore : Store}
    (evaluation : Evaluates actual store code value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  rw [emitted] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    entry.reflects functions extension definitions registered program contextValid unique uninitialized missing certificate bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, entry.environment, entry.heap, outcome, after, finalMap, finalWorld, owned, history,
    entry.allocation, trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, reached⟩

end Solcore.SourceSemantics.CoreLowering.TypedMixedNamedParameters.Indexed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedNamedParameterMeaning
/-! Parameter installation reaches the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
body correspondence comes from the extracted fixed-context certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedNamedParameters
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

structure Entry (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings actualContext) ambient.definitions
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

/-- Every source/native parameter fact is constructed before running the body.
The call context is fixed by the independent monomorphic binder extension. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body) := by
  obtain ⟨environment, heap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, frame, lookups, finalTyped, agreement⟩ :=
    CallableIndexedParameterTyped.named_prefix onError accepted inputs definitions registered represented environments heaps
      actualLayout actualTyped reference read unmapped
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  exact ⟨⟨environment, heap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, finalEnvironments, finalHeaps, GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, frame, GenericLexicalContext.binders_metadata allocated, lookups, finalTyped, agreement⟩⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry) (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}

include extension contextValid unique uninitialized missing in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem Entry.preserves
    (entry : Entry values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : TypedNamedBody.Certificate readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    certificate.preserves functions extension program contextValid unique uninitialized missing entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

include extension contextValid unique uninitialized missing in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem Entry.reflects
    (entry : Entry values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : TypedNamedBody.Certificate readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    certificate.reflects functions extension program contextValid unique uninitialized missing entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedNamedParameters
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedNamedParameterIndexed
/-! The actual named hook encloses the complete marked parameter prefix. Its
body certificate is applied only at the installed call context. Native and
source parameter allocations precede that continuation, and the caller frame
and protected snapshots are restored after either represented body outcome. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedNamedParameters.Indexed
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (certificate : TypedNamedBody.Certificate readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named (parameterCode.rename ξ) = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- A source allocation and its finite body trace execute the real full named
hook. Parameters are compared with the independently constructed allocation. -/
theorem preserves {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store code value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    entry.preserves functions extension program contextValid unique uninitialized missing certificate trace
  rw [rename_prefix] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var actualReference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    emitted.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing actualTyped in
/-- Completed actual native execution constructs both source parameter
allocation and the independent body trace at the fixed call context. -/
theorem reflects {value : Value} {finalStore : Store}
    (evaluation : Evaluates actual store code value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  rw [emitted] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    entry.reflects functions extension program contextValid unique uninitialized missing certificate bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, entry.environment, entry.heap, outcome, after, finalMap, finalWorld, owned, history,
    entry.allocation, trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

end Solcore.SourceSemantics.CoreLowering.TypedNamedParameters.Indexed
end
