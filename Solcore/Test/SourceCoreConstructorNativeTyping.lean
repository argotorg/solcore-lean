import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping

/-! Registered production headers and recursively extracted child code supply
native typing. The consumer retains raw metadata and source constructor facts,
instead of attempting to reconstruct either from a native named-data type. -/
set_option autoImplicit false
namespace Tests.SourceCoreConstructorNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping

/-- An actual contextual compiler result needs no separately supplied child
code typing, even with arbitrary hidden slots and extra ambient definitions. -/
theorem actual_contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : CompatibleExpressionConstructors.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  CompatibleExpressionConstructorNativeTyping.contextual_native visibleTypes administrative
    ordinary unique closed residual declarations syntaxTree found typed readPolicy lowerPolicy leafPolicy accepted extension

/-- Recursive constructor children close their own native typing. Only the
existing source-static trees and actual registered header are inputs. -/
theorem actual_header_native
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {ids : List ExpressionId} {tag : ConstructorId} {header : Word}
    {codes : List SourceCoreBasic.LoweredExpr} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
    (children : ∀ child code, (child, code) ∈ ids.zip codes →
      CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope child code)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative)
      ⟨.namedData tag.owner,
        SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ :=
  constructors_native_at visibleTypes administrative extension
    (.constructor receipt form valid count nodes children)

/-- Native constructor typing requires the exact registered payload shape.
A type for its inhabited argument cannot invent an absent constructor. -/
theorem absent_constructor_rejected (tag : ConstructorId) (header : Word) (context : Core.Context) :
    ¬ HasType context (SourceCoreCompatibleDataExpressions.construct tag header
      (LanguageResult.success .unit)) (LanguageResult.resultType (.namedData tag.owner)) [] := by
  intro typed
  simp only [SourceCoreCompatibleDataExpressions.construct, LanguageResult.bind] at typed
  cases typed with
  | caseE _ failed _ =>
    cases failed with
    | inLeft registered _ =>
      cases registered with
      | namedData found => cases found

end Tests.SourceCoreConstructorNativeTyping
