import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyTree
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree

/-! One mixed statement tree retains ordinary and generalized declarations,
fallthrough, returns and scoped control. Every child is a static compiler
certificate; exact marked allocation packets and native code are preserved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTree
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open TypedLexicalWhile (initializedRequest sequence)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → SourceCoreLocalCell.Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil {sourceContext scope mode expected type} (allowed : mode = false ∨ expected = .unit) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode []
        expected type (LocalLoop.fallthrough type)
  | returnUnit {sourceContext scope mode id node} (rest : List StatementId)
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .returnStmt none) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        .unit .unit (LocalLoop.returned .unit)
  | returning {sourceContext scope mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {sourceContext scope id node expression expressionNode expected lowered}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .expression expression false)
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope true [id]
        expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)
  | generalizedInitialized {sourceContext nextContext scope mode id node binder initializer initializerNode parameters result lambdaBody rest expected type lowered body childFuel}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = [])
      (coercions : initializerNode.coercions = [])
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key [] (source named) binder initializer)
      (initial : GeneralizedLocalInitializerPackets.Receipt prepared
        (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
          (context prepared named) scope initializer reasonAt) site.binding [] lowered)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (sequence type lowered.expression annotation.expression body)
  | initialized {sourceContext nextContext scope mode id node binder initializer initializerNode rest expected type lowered body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) sourceContext initializer initializerNode.type)
      (value : certificates sourceContext scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (sequence type lowered.expression annotation.expression body)

  | uninitialized {sourceContext nextContext scope mode id node binder rest expected type body payload}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder none)
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner sourceContext binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (.letE annotation.expression body)

  | discard {sourceContext scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (continuing : semicolon = true ∨ mode = false)
      (expressionFound : (source named).lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType (source named) sourceContext expression expressionNode.type)
      (value : certificates sourceContext scope expression lowered)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {sourceContext scope mode id node statements rest expected type innerCode body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .block statements)
      (inner : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope false statements expected type innerCode)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.sequence type innerCode body)
  | ifThen {sourceContext scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : (source named).lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTyped : ExpressionHasType (source named) sourceContext condition conditionNode.type)
      (conditionCertificate : certificates sourceContext scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope false thenBody expected type thenCode)
      (elseTree : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree prepared named compiled certificates administrative reasonAt
        sourceContext scope mode rest expected type body) :
      Tree prepared named compiled certificates administrative reasonAt sourceContext scope mode (id :: rest)
        expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTree
