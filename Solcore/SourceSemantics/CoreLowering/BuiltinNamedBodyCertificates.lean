import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
import Solcore.SourceSemantics.CoreLowering.NamedCompilationReceipt

/-! Static receipts for the ordinary lexical named-body fragment with recursive builtin expressions. A receipt
retains the actual production traversal equation and its extracted statement
tree at its initial source context. It contains no body execution or semantic induction
hypothesis. Context/evidence validity remains a separate static obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
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
  projection : values.checked.catalog.project expected = .ok type
  syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected
  flow : Expr
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope true
    statements expected type flow

/-- Static extraction can also retain an already extracted production flow.
The actual body action and finish equation remain required; there is no
execution field or semantic hypothesis in this factory. -/
theorem of_tree
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
    {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (emitted : code = CompatibleStatements.finish type flow fellThrough escaped)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values
      source solved reasonAt context scope true statements expected type flow) :
    Nonempty (Certificate layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :=
  ⟨⟨accepted, projection, syntaxTree, flow, emitted, tree⟩⟩

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
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy}
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
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
      signatures locals parents assignments diagnostics compilation (some native) parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    Nonempty (Certificate layouts owner active frame globals onError readFuel values source context compilation.solvedRequirements reasonAt scope
      statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, emitted, tree⟩ := BuiltinLexicalStatements.tree_of_contextual_body ordinary unique closed residual sourceSignatures
    declarations readExpression lowerRead leafLowerer readStatement representationBinder lowerBinder sourceCells lowerExpression syntaxTree projection accepted
  exact ⟨⟨accepted, projection, syntaxTree, flow, emitted, tree⟩⟩

/-- Instantiate the generic named compiler decomposition with the concrete
lexical builtin-statement tree, at the actual scope after parameter installation.
All context/evidence/ordinary obligations are explicit static hypotheses. -/
theorem compilation_of_accepted
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {allocationGlobals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {locals : SourceCoreLocalPolymorphism.Catalog}
    {native : SourceCoreGeneralFunctions.CallableContext}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {named : SourceCoreGeneralFunctions.Function}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {readFuel fuel : Nat} {values : SourceCoreCompatibleValues.Context} {code : Expr}
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan
      (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionBuiltins.Ordinary function.source locals named.signature.key)
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
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression program (representation.atContext named.signature.key [])
        signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native) none none)
    (representationBinder : (representation.atContext named.signature.key []).expressions.lowerBinder =
      SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).lowerBinder =
      SourceCoreGeneralFunctions.contextualBinder (representation.atContext named.signature.key []) locals named.signature.key [])
    (sourceCells : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)))
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)))
    (syntaxTree : BuiltinLexicalStatements.Syntax function.source context true function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals (some native) fuel named = .ok code) :
    Nonempty (NamedCompilationReceipt.Receipt program representation signatures plan globals diagnostics locals (some native) parents own
      named function.body fuel
      (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)) (fun body => Nonempty (Certificate layouts owner active frame allocationGlobals onError readFuel values function.source context
        named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType
        named.signature.resultType (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key [])
          program signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native))
        fuel own.fellThroughReason own.table.escapedReason body)) code) := by
  apply NamedCompilationReceipt.of_accepted (agreement.source ▸ agreement.roots) parentReceipt diagnosticReceipt allocator ?_ accepted
  intro body lowered
  change SourceCoreLoops.lowerStatementsWithPolicy _ _ _ _ _ _ _ _ _ = .ok body at lowered
  rw [← agreement.source] at lowered
  exact of_contextual ordinary unique closed residual declarations sourceSignatures readExpression lowerRead leafLowerer
    readStatement representationBinder lowerBinder sourceCells lowerExpression syntaxTree projection lowered

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
