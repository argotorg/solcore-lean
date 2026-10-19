import Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree

/-! A selected named body keeps ordinary terminal expressions and generalized
native bundle declarations in one lexical tree. Actual marked allocations and
compiler candidate rows remain attached to each declaration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyTree
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

end Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyTree
