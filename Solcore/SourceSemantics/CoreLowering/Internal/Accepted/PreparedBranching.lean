import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedMatches
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedPlans
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.Frontend.SourceCoreLocalPolymorphism
import Lean

/-!
# Prepared branching and local origins

Catalog sites and syntax of prepared branching bodies, and the origins and metadata of prepared local instances.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
/-! Actual projected preparation remains attached to the original occurrence.
Its mapping diagnostics are interpreted only at the reached typed state; bare
heads retain the existing static diagnostic receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
open Core Frontend SourceInference

inductive AssignmentSite
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs) : Prop where
  | existing (errors : head.ReachableErrors registry faults) :
      AssignmentSite invalidProjection missingDefault registry faults head
  | projected {site : SourceCoreElaboration.ErrorSite} {fuel : Nat}
      (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
      (signatures : context.signatures = values.checked.signatures)
      (nonempty : assignment.target.projections ≠ [])
      (retained : head.PreparedAt site fuel (invalidProjection site assignment.target.root)
        (missingDefault site assignment.target.root))
      (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid) :
      AssignmentSite invalidProjection missingDefault registry faults head

/-- Unary preparation retains its actual owner and keys without a Source RHS. -/
inductive UnarySite
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution}
    (head : CompatibleProjectedBitNotStatements.Head values source context certificate scope administrative definitions assignment) : Prop where
  | projected {site : SourceCoreElaboration.ErrorSite} {fuel : Nat}
      (origin : ProjectedBitNotDiagnosticOrigins.Occurs source site assignment)
      (signatures : context.signatures = values.checked.signatures)
      (nonempty : assignment.target.projections ≠ [])
      (retained : head.PreparedAt site fuel (invalidProjection site assignment.target.root)
        (missingDefault site assignment.target.root)) :
      UnarySite invalidProjection missingDefault head

section Headers
open GenericForHeader
open TypedLexicalWhile (absentRequest initializedRequest)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}

variable (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
  (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
inductive HeaderSites (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {items : List ForItemForm} → {code : Expr} →
    Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code → Prop where
  | nil {context scope code}
      {next : continuation context scope code}
      : HeaderSites invalidProjection missingDefault registry faults (.nil next)
  | uninitialized {context nextContext scope binder rest body payload}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body}
      (remainingErrors : HeaderSites invalidProjection missingDefault registry faults remaining)
      : HeaderSites invalidProjection missingDefault registry faults (.uninitialized monomorphic extended ordinary projected allocation annotation same remaining)
  | initialized {context nextContext scope binder initializer initializerNode lowered body rest}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body}
      (remainingErrors : HeaderSites invalidProjection missingDefault registry faults remaining)
      : HeaderSites invalidProjection missingDefault registry faults (.initialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope expression expressionNode rest lowered body}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : HeaderSites invalidProjection missingDefault registry faults remaining)
      : HeaderSites invalidProjection missingDefault registry faults (.discard found value remaining)
  | assign {context scope assignment operator rhs rest body}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : HeaderSites invalidProjection missingDefault registry faults remaining)
      (headErrors : AssignmentSite invalidProjection missingDefault registry faults head)
      : HeaderSites invalidProjection missingDefault registry faults (.assign head remaining)
  | bitNot {context scope assignment rest body}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : HeaderSites invalidProjection missingDefault registry faults remaining)
      (headErrors : head.Errors faults)
      : HeaderSites invalidProjection missingDefault registry faults (.bitNot head remaining)

  | bitNotProjected {context scope assignment rest body}
      {head : CompatibleProjectedBitNotStatements.Head values source context (certificates context) scope administrative definitions assignment}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : HeaderSites invalidProjection missingDefault registry faults remaining)
      (headErrors : UnarySite invalidProjection missingDefault head)
      : HeaderSites invalidProjection missingDefault registry faults (.bitNotProjected head remaining)

end Headers

section Bodies
open GenericImperativeMatch
open GenericImperativeMatch.Tree (MatchContextFields)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

variable (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
  (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
inductive CatalogSites (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {position : Position} →
    {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code → Prop where
  | body {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code}
      : CatalogSites invalidProjection missingDefault registry faults (.body syntaxTree body)
  | uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder none}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder (some initializer)}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.discard found form notTail expressionFound value remaining)
  | block {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (innerErrors : CatalogSites invalidProjection missingDefault registry faults inner)
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.block found form inner remaining)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (thenTreeErrors : CatalogSites invalidProjection missingDefault registry faults thenTree)
      (elseTreeErrors : CatalogSites invalidProjection missingDefault registry faults elseTree)
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining)
  | breaking {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt}
      : CatalogSites invalidProjection missingDefault registry faults (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
  | continuing {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt}
      : CatalogSites invalidProjection missingDefault registry faults (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
  | whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .whileLoop condition statements}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (loopBodyErrors : CatalogSites invalidProjection missingDefault registry faults loopBody)
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining)
  | assign {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      (headErrors : AssignmentSite invalidProjection missingDefault registry faults head)
      : CatalogSites invalidProjection missingDefault registry faults (.assign found form head remaining)

  | bitNot {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      (headErrors : head.Errors faults)
      : CatalogSites invalidProjection missingDefault registry faults (.bitNot found form head remaining)

  | bitNotProjected {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleProjectedBitNotStatements.Head values source context (certificates context) scope administrative definitions assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      (headErrors : UnarySite invalidProjection missingDefault head)
      : CatalogSites invalidProjection missingDefault registry faults (.bitNotProjected found form head remaining)

  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (initialErrors : CatalogSites invalidProjection missingDefault registry faults initial) (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining) :
      CatalogSites invalidProjection missingDefault registry faults (.forLoop found form initial remaining)
  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (loopErrors : CatalogSites invalidProjection missingDefault registry faults loopBody) (postErrors : HeaderSites invalidProjection missingDefault registry faults postTree) :
      CatalogSites invalidProjection missingDefault registry faults (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped)
  | initializerUninitialized {context nextContext scope binder rest body payload condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining)
  | initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      : CatalogSites invalidProjection missingDefault registry faults (.initializerDiscard found value remaining)
  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      (headErrors : AssignmentSite invalidProjection missingDefault registry faults head)
      : CatalogSites invalidProjection missingDefault registry faults (.initializerAssign head remaining)
  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      (headErrors : head.Errors faults)
      : CatalogSites invalidProjection missingDefault registry faults (.initializerBitNot head remaining)
  | initializerBitNotProjected {context scope assignment rest body condition post statements expected type}
      {head : CompatibleProjectedBitNotStatements.Head values source context (certificates context) scope administrative definitions assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining)
      (headErrors : UnarySite invalidProjection missingDefault head)
      : CatalogSites invalidProjection missingDefault registry faults (.initializerBitNotProjected head remaining)
  | matchWith {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node} (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (catalog : SignatureCatalogWellFormed values.checked.signatures)
      (patternContext : MatchContextFields compilation context)
      (childErrors : ∀ request member childContext valid, CatalogSites invalidProjection missingDefault registry faults (children request member childContext valid))
      (remainingErrors : CatalogSites invalidProjection missingDefault registry faults remaining) :
      CatalogSites invalidProjection missingDefault registry faults (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children remaining)

  | terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type innerCode}
      {stops : GenericLexicalStatements.Stopped source statements}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (innerErrors : CatalogSites invalidProjection missingDefault registry faults inner) :
      CatalogSites invalidProjection missingDefault registry faults (.terminalBlock unique found form inner stops issued)
  | terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .ifThen condition thenBody (some elseBody)}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false elseBody) expected type elseCode}
      {thenStops : GenericLexicalStatements.Stopped source thenBody}
      {elseStops : GenericLexicalStatements.Stopped source elseBody}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (thenErrors : CatalogSites invalidProjection missingDefault registry faults thenTree)
      (elseErrors : CatalogSites invalidProjection missingDefault registry faults elseTree) :
      CatalogSites invalidProjection missingDefault registry faults
        (.terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)

  | terminalMatch {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {stops : ReachableMatchContinuations.DefaultStopped source id resolution}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (catalog : SignatureCatalogWellFormed values.checked.signatures)
      (patternContext : MatchContextFields compilation context)
      (childErrors : ∀ request member childContext valid, CatalogSites invalidProjection missingDefault registry faults (children request member childContext valid))
      :
      CatalogSites invalidProjection missingDefault registry faults (.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children stops issued)


end Bodies
end Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
open Core Frontend SourceInference

theorem operands {source : TypedSource} {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    {faults : FunctionCalls.FaultRep}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (included : ∀ reason word, GenericAssignmentDiagnostics.OperandRep table reason word → faults reason word)
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (profile : operator = .equal ∨ assignment.target.type = .word) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator
      (GenericAssignmentDiagnostics.token table site assignment.target.root operator) := by
  have raw : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false :=
    profile.elim Or.inl (fun word => .inr (.inl word))
  cases origin with
  | statement found form =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands_included included prepared present.1 (.statement form) raw
  | header found form member =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands_included included prepared present.1 (.header form member) raw

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingBareUnarySyntax
/-! Returned lambda bodies keep the original unary grammar until their
prepared body packet supports projected unary updates. Value assignments and
all existing nested control remain available. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingBareUnarySyntax
open Core Frontend SourceInference

def Header (items : List ForItemForm) : Prop :=
  ∀ assignment, .assignBitNot assignment ∈ items → assignment.target.projections = []

mutual
inductive Body (source : TypedSource) : List StatementId → Prop where
  | nil : Body source []
  | cons {id node rest} (found : source.lookupStatement? id = some node)
      (head : Form source node.form) (tail : Body source rest) : Body source (id :: rest)
inductive Form (source : TypedSource) : StatementForm → Prop where
  | leaf {form} (allowed : (match form with
      | .assignBitNot _ | .block _ | .ifThen _ _ _ | .whileLoop _ _ | .forLoop _ _ _ _ | .matchWith _ => False
      | _ => True)) : Form source form
  | bitNot {assignment} (bare : assignment.target.projections = []) : Form source (.assignBitNot assignment)
  | block {statements} (inner : Body source statements) : Form source (.block statements)
  | conditional {condition left right} (first : Body source left) (second : Body source (right.getD [])) :
      Form source (.ifThen condition left right)
  | whileLoop {condition statements} (inner : Body source statements) : Form source (.whileLoop condition statements)
  | forLoop {initial condition post statements} (before : Header initial) (after : Header post)
      (inner : Body source statements) : Form source (.forLoop initial condition post statements)
  | matchWith {resolution} (arms : ∀ arm ∈ resolution.cases, Body source arm.body)
      (fallback : Body source (resolution.defaultBody.getD [])) : Form source (.matchWith resolution)
end

def Position (source : TypedSource) : GenericImperativeMatch.Position → Prop
  | .statements _ statements => Body source statements
  | .initializers items _ post statements => Header items ∧ Header post ∧ Body source statements

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by intro item member; rcases List.mem_cons.mp member with rfl | member
               · exact head
               · exact tail item member⟩

private def header? (items : List ForItemForm) : Option (PLift (Header items)) := do
  let ⟨found⟩ ← allProof? (fun item => ∀ assignment, item = .assignBitNot assignment → assignment.target.projections = [])
    (fun item => by
      cases item with
      | assignBitNot assignment =>
        exact if bare : assignment.target.projections = [] then
          some ⟨by intro actual same; cases same; exact bare⟩ else none
      | letDecl | expression | assignValue => exact some ⟨by intro actual same; cases same⟩) items
  pure ⟨fun assignment member => found _ member assignment rfl⟩

mutual
private def body? (source : TypedSource) : (fuel : Nat) → (statements : List StatementId) → Option (PLift (Body source statements))
  | _, [] => some ⟨.nil⟩
  | 0, _ :: _ => none
  | fuel + 1, id :: rest => do
      match found : source.lookupStatement? id with
      | none => none
      | some node =>
        let ⟨head⟩ ← form? source fuel node.form
        let ⟨tail⟩ ← body? source fuel rest
        pure ⟨.cons found head tail⟩
private def form? (source : TypedSource) : (fuel : Nat) → (form : StatementForm) → Option (PLift (Form source form))
  | 0, _ => none
  | fuel + 1, form => by
      cases form with
      | assignBitNot assignment =>
        exact if bare : assignment.target.projections = [] then some ⟨.bitNot bare⟩ else none
      | block statements => exact do
        let ⟨inner⟩ ← body? source fuel statements
        pure ⟨.block inner⟩
      | ifThen condition left right => exact do
        let ⟨first⟩ ← body? source fuel left
        let ⟨second⟩ ← body? source fuel (right.getD [])
        pure ⟨.conditional first second⟩
      | whileLoop condition statements => exact do
        let ⟨inner⟩ ← body? source fuel statements
        pure ⟨.whileLoop inner⟩
      | forLoop initial condition post statements => exact do
        let ⟨before⟩ ← header? initial
        let ⟨after⟩ ← header? post
        let ⟨inner⟩ ← body? source fuel statements
        pure ⟨.forLoop before after inner⟩
      | matchWith resolution => exact do
        let ⟨arms⟩ ← allProof? (fun arm : TypedMatchCase => Body source arm.body)
          (fun arm => body? source fuel arm.body) resolution.cases
        let ⟨fallback⟩ ← body? source fuel (resolution.defaultBody.getD [])
        pure ⟨.matchWith arms fallback⟩
      | returnStmt | letDecl | expression | breakStmt | continueStmt | assignValue => exact some ⟨.leaf True.intro⟩
end

def check (source : TypedSource) (statements : List StatementId) : Option (PLift (Body source statements)) :=
  body? source (2 * (source.nodes.length + 1)) statements

theorem Header.tail {item rest} (header : Header (item :: rest)) : Header rest :=
  fun assignment member => header assignment (List.mem_cons_of_mem item member)

theorem Body.tail {source id rest} (body : Body source (id :: rest)) : Body source rest := by
  cases body with | cons _ _ tail => exact tail

theorem Body.head {source id node rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) : Form source node.form := by
  cases body with
  | cons actual head tail =>
    cases Option.some.inj (actual.symm.trans found)
    exact head

theorem Body.unary {source id node assignment rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment) :
    assignment.target.projections = [] := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | bitNot bare => exact bare

theorem Body.block {source id node statements rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements) : Body source statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | block inner => exact inner

theorem Body.branches {source id node condition left right rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right) :
    Body source left ∧ Body source (right.getD []) := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | conditional first second => exact ⟨first, second⟩

theorem Body.loop {source id node condition statements rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements) : Body source statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | whileLoop inner => exact inner

theorem Body.for_children {source id node initial condition post statements rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initial condition post statements) :
    Header initial ∧ Header post ∧ Body source statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | forLoop before after inner => exact ⟨before, after, inner⟩

theorem Body.match_request {source id node resolution rest parent type request childContext}
    (body : Body source (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (context : GenericMatchChildren.ContextFor source parent type resolution.cases resolution.defaultBody request childContext) :
    Body source request.statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | matchWith arms fallback =>
    cases context with
    | arm member statements _ _ => rw [statements]; exact arms _ member
    | default statements => simpa only [statements, Option.getD_some] using fallback

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingBareUnarySyntax

namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference
open PreparedBranchingBareUnarySyntax

theorem GenericForHeader.PreparedSyntax.bareUnary {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {items : List ForItemForm}
    (tree : GenericForHeader.PreparedSyntax source approved context items) (shape : Header items) :
    GenericForHeader.Syntax source approved context items := by
  revert shape
  induction tree with
  | nil => intro _; exact .nil
  | uninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized declaration mono extended ordinary (ih shape.tail)
  | initialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized declaration mono extended ordinary found sourceType typed syntaxTree (ih shape.tail)
  | discard found typed syntaxTree remaining ih =>
    intro shape
    exact .discard found typed syntaxTree (ih shape.tail)
  | assign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign sourceTyped writable rightTyped profile children (ih shape.tail)
  | bitNot writable bare profile remaining ih =>
    intro shape
    exact .bitNot writable bare profile (ih shape.tail)
  | bitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape _ List.mem_cons_self))

theorem GenericImperativeMatch.PreparedSyntax.bareUnary {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (tree : GenericImperativeMatch.PreparedSyntax source approved context position expected)
    (shape : PreparedBranchingBareUnarySyntax.Position source position) : GenericImperativeMatch.Syntax source approved context position expected := by
  revert shape
  induction tree with
  | body syntaxTree => intro _; exact .body syntaxTree
  | uninitialized found form declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized found form declaration mono extended ordinary (ih shape.tail)
  | initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree (ih shape.tail)
  | discard found form notTail sourceType expressionFound typed syntaxTree remaining ih =>
    intro shape
    exact .discard found form notTail sourceType expressionFound typed syntaxTree (ih shape.tail)
  | block found form sourceType inner remaining innerIH restIH =>
    intro shape
    exact .block found form sourceType (innerIH (shape.block found form)) (restIH shape.tail)
  | ifThen found form sourceType conditionFound conditionType typed syntaxTree left right remaining leftIH rightIH restIH =>
    intro shape
    exact .ifThen found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2) (restIH shape.tail)
  | breaking found form => intro _; exact .breaking found form
  | continuing found form => intro _; exact .continuing found form
  | whileLoop found form conditionFound conditionType typed syntaxTree inner remaining innerIH restIH =>
    intro shape
    exact .whileLoop found form conditionFound conditionType typed syntaxTree
      (innerIH (shape.loop found form)) (restIH shape.tail)
  | assign found form sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign found form sourceTyped writable rightTyped profile children (ih shape.tail)
  | forLoop found form sourceType initial remaining initialIH restIH =>
    intro shape
    have parts := shape.for_children found form
    exact .forLoop found form sourceType (initialIH parts) (restIH shape.tail)
  | initializersDone found sourceType typed syntaxTree loop post ih =>
    intro shape
    exact .initializersDone found sourceType typed syntaxTree (ih shape.2.2) (post.bareUnary shape.2.1)
  | initializerUninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .initializerUninitialized declaration mono extended ordinary (ih ⟨shape.1.tail, shape.2⟩)
  | initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree (ih ⟨shape.1.tail, shape.2⟩)
  | initializerDiscard found typed syntaxTree remaining ih =>
    intro shape
    exact .initializerDiscard found typed syntaxTree (ih ⟨shape.1.tail, shape.2⟩)
  | initializerAssign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .initializerAssign sourceTyped writable rightTyped profile children (ih ⟨shape.1.tail, shape.2⟩)
  | bitNot found form writable bare profile remaining ih =>
    intro shape
    exact .bitNot found form writable bare profile (ih shape.tail)
  | bitNotProjected found form _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape.unary found form))
  | initializerBitNot writable bare profile remaining ih =>
    intro shape
    exact .initializerBitNot writable bare profile (ih ⟨shape.1.tail, shape.2⟩)
  | initializerBitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape.1 _ List.mem_cons_self))
  | matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children remaining childrenIH restIH =>
    intro shape
    exact .matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid))
      (restIH shape.tail)
  | terminalBlock unique found form sourceType inner stops ih =>
    intro shape
    exact .terminalBlock unique found form sourceType (ih (shape.block found form)) stops
  | terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree left right leftStops rightStops leftIH rightIH =>
    intro shape
    exact .terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2) leftStops rightStops
  | terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children stops childrenIH =>
    intro shape
    exact .terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid)) stops
  | scopedBlock found form inner remaining innerIH restIH =>
    intro shape
    exact .scopedBlock found form (innerIH (shape.block found form)) (restIH shape.tail)

end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingLegacySyntax
/-! The original source shape excludes projected unary nodes when an older
uniform diagnostic API requires its original syntax grammar. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedLegacyBranchingTree

theorem GenericForHeader.PreparedSyntax.legacy {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {items : List ForItemForm}
    (tree : GenericForHeader.PreparedSyntax source approved context items) (shape : ItemShape items) :
    GenericForHeader.Syntax source approved context items := by
  revert shape
  induction tree with
  | nil => intro _; exact .nil
  | uninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized declaration mono extended ordinary (ih shape.let_tail)
  | initialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized declaration mono extended ordinary found sourceType typed syntaxTree (ih shape.let_tail)
  | discard found typed syntaxTree remaining ih =>
    intro shape
    exact .discard found typed syntaxTree (ih shape.discard_tail)
  | assign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign sourceTyped writable rightTyped profile children (ih shape.assign_tail.2.2)
  | bitNot writable bare profile remaining ih =>
    intro shape
    exact .bitNot writable bare profile (ih shape.bitNot_tail.2.2)
  | bitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected shape.bitNot_tail.2.1)

theorem GenericImperativeMatch.PreparedSyntax.legacy {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (tree : GenericImperativeMatch.PreparedSyntax source approved context position expected)
    (shape : PositionShape source position) : GenericImperativeMatch.Syntax source approved context position expected := by
  revert shape
  induction tree with
  | body syntaxTree => intro _; exact .body syntaxTree
  | uninitialized found form declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized found form declaration mono extended ordinary (ih (shape.tail_of_let found form))
  | initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree (ih (shape.tail_of_let found form))
  | discard found form notTail sourceType expressionFound typed syntaxTree remaining ih =>
    intro shape
    exact .discard found form notTail sourceType expressionFound typed syntaxTree (ih (shape.discard_tail found form notTail).2)
  | block found form sourceType inner remaining innerIH restIH =>
    intro shape
    exact .block found form sourceType (innerIH (shape.block_children found form).1) (restIH (shape.block_children found form).2)
  | ifThen found form sourceType conditionFound conditionType typed syntaxTree left right remaining leftIH rightIH restIH =>
    intro shape
    exact .ifThen found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2.1) (restIH (shape.branches found form).2.2)
  | breaking found form => intro _; exact .breaking found form
  | continuing found form => intro _; exact .continuing found form
  | whileLoop found form conditionFound conditionType typed syntaxTree inner remaining innerIH restIH =>
    intro shape
    exact .whileLoop found form conditionFound conditionType typed syntaxTree
      (innerIH (shape.loop found form).1) (restIH (shape.loop found form).2)
  | assign found form sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign found form sourceTyped writable rightTyped profile children (ih (shape.assign_tail found form).2.2)
  | forLoop found form sourceType initial remaining initialIH restIH =>
    intro shape
    have parts := shape.for_children found form
    exact .forLoop found form sourceType (initialIH ⟨parts.1, parts.2.1, parts.2.2.1⟩) (restIH parts.2.2.2)
  | initializersDone found sourceType typed syntaxTree loop post ih =>
    intro shape
    exact .initializersDone found sourceType typed syntaxTree (ih shape.2.2) (post.legacy shape.2.1)
  | initializerUninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .initializerUninitialized declaration mono extended ordinary (ih ⟨shape.1.let_tail, shape.2⟩)
  | initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree (ih ⟨shape.1.let_tail, shape.2⟩)
  | initializerDiscard found typed syntaxTree remaining ih =>
    intro shape
    exact .initializerDiscard found typed syntaxTree (ih ⟨shape.1.discard_tail, shape.2⟩)
  | initializerAssign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .initializerAssign sourceTyped writable rightTyped profile children (ih ⟨shape.1.assign_tail.2.2, shape.2⟩)
  | bitNot found form writable bare profile remaining ih =>
    intro shape
    exact .bitNot found form writable bare profile (ih (shape.bitNot_tail found form).2.2)
  | bitNotProjected found form _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape.bitNot_tail found form).2.1)
  | initializerBitNot writable bare profile remaining ih =>
    intro shape
    exact .initializerBitNot writable bare profile (ih ⟨shape.1.bitNot_tail.2.2, shape.2⟩)
  | initializerBitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected shape.1.bitNot_tail.2.1)
  | matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children remaining childrenIH restIH =>
    intro shape
    exact .matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid))
      (restIH (shape.match_children found form).2.2)
  | terminalBlock unique found form sourceType inner stops ih =>
    intro shape
    exact .terminalBlock unique found form sourceType (ih (shape.block_children found form).1) stops
  | terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree left right leftStops rightStops leftIH rightIH =>
    intro shape
    exact .terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2.1) leftStops rightStops
  | terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children stops childrenIH =>
    intro shape
    exact .terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid)) stops
  | scopedBlock found form inner remaining innerIH restIH =>
    intro shape
    exact .scopedBlock found form (innerIH (shape.block_children found form).1) (restIH (shape.block_children found form).2)

end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingLegacyCatalogSites
/-! The original bare assignment grammar projects prepared catalogs to the
legacy uniform diagnostic receipt. Projected branches remain excluded here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingLegacyCatalogSites
open Core Frontend SourceInference
open PreparedBranchingCatalogSites
open CallableIndexedOwnedPreparedStagedLegacyBranchingTree
variable {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

theorem assignment {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {resolution : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions resolution operator rhs}
    (site : AssignmentSite invalidProjection missingDefault registry faults head)
    (bare : resolution.target.projections = []) : head.ReachableErrors registry faults := by
  cases site with
  | existing errors => exact errors
  | projected _ _ nonempty _ _ => exact False.elim (nonempty bare)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem header {type : Ty} {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    {context scope items code}
    {tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code}
    (sites : HeaderSites invalidProjection missingDefault registry faults tree)
    (shape : ItemShape items) : tree.ErrorsFor .reachable registry faults := by
  revert shape
  refine HeaderSites.rec (motive := fun {context scope items code} tree _ =>
    ItemShape items → tree.ErrorsFor .reachable registry faults) ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope code next shape
    exact GenericForHeader.Tree.ErrorsFor.nil (context := context) (scope := scope) (code := code) (next := next)
  · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih shape
    exact GenericForHeader.Tree.ErrorsFor.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (ih shape.let_tail)
  · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining remainingErrors ih shape
    exact GenericForHeader.Tree.ErrorsFor.initialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (ih shape.let_tail)
  · intro context scope expression expressionNode rest lowered body found value remaining remainingErrors ih shape
    exact GenericForHeader.Tree.ErrorsFor.discard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (found := found) (value := value) (remaining := remaining) (ih shape.discard_tail)
  · intro context scope assignment operator rhs rest body head remaining remainingErrors receipt ih shape
    exact GenericForHeader.Tree.ErrorsFor.assign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (head := head) (remaining := remaining) (ih shape.assign_tail.2.2) (PreparedBranchingLegacyCatalogSites.assignment receipt shape.assign_tail.2.1)
  · intro context scope assignment rest body head remaining remainingErrors receipt ih shape
    exact GenericForHeader.Tree.ErrorsFor.bitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (head := head) (remaining := remaining) (ih shape.bitNot_tail.2.2) receipt
  · intro context scope assignment rest body head remaining remainingErrors receipt ih shape
    exact False.elim (head.projected shape.bitNot_tail.2.1)

open GenericImperativeMatch

theorem body {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (sites : CatalogSites invalidProjection missingDefault registry faults tree)
    (shape : PositionShape source position) : tree.CatalogSites .reachable registry faults := by
  revert shape
  refine CatalogSites.rec (motive := fun {context scope position expected type code} tree _ =>
    PositionShape source position → tree.CatalogSites .reachable registry faults)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope mode statements expected type code syntaxTree body shape
    exact Tree.CatalogSites.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH (shape.tail_of_let found form))
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH (shape.tail_of_let found form))
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining) (remainingErrorsIH (shape.discard_tail found form notTail).2)
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining) (innerErrorsIH (shape.block_children found form).1) (remainingErrorsIH (shape.block_children found form).2)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining) (thenTreeErrorsIH (shape.branches found form).1) (elseTreeErrorsIH (shape.branches found form).2.1) (remainingErrorsIH (shape.branches found form).2.2)
  · intro context scope mode id node rest expected type found form shape
    exact Tree.CatalogSites.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node rest expected type found form shape
    exact Tree.CatalogSites.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining) (loopBodyErrorsIH (shape.loop found form).1) (remainingErrorsIH (shape.loop found form).2)
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (remainingErrorsIH (shape.assign_tail found form).2.2) (PreparedBranchingLegacyCatalogSites.assignment headErrors (shape.assign_tail found form).2.1)
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (remainingErrorsIH (shape.bitNot_tail found form).2.2) headErrors
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH shape
    exact False.elim (head.projected (shape.bitNot_tail found form).2.1)
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsIH remainingErrorsIH shape
    have parts := shape.for_children found form
    exact Tree.CatalogSites.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining) (initialErrorsIH ⟨parts.1, parts.2.1, parts.2.2.1⟩) (remainingErrorsIH parts.2.2.2)
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsIH shape
    exact Tree.CatalogSites.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped) (loopErrorsIH shape.2.2) (header postErrors shape.2.1)
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH ⟨shape.1.let_tail, shape.2⟩)
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrorsIH ⟨shape.1.let_tail, shape.2⟩)
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining) (remainingErrorsIH ⟨shape.1.discard_tail, shape.2⟩)
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (remainingErrorsIH ⟨shape.1.assign_tail.2.2, shape.2⟩) (PreparedBranchingLegacyCatalogSites.assignment headErrors shape.1.assign_tail.2.1)
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH shape
    exact Tree.CatalogSites.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (remainingErrorsIH ⟨shape.1.bitNot_tail.2.2, shape.2⟩) headErrors
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH shape
    exact False.elim (head.projected shape.1.bitNot_tail.2.1)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog patternContext childErrors remainingErrors childErrorsIH remainingErrorsIH shape
    exact Tree.CatalogSites.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining) catalog patternContext (fun request member childContext valid => childErrorsIH request member childContext valid (shape.match_request found form valid.forget)) (remainingErrorsIH (shape.match_children found form).2.2)
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerErrorsIH shape
    exact Tree.CatalogSites.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued) (innerErrorsIH (shape.block_children found form).1)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenErrorsIH elseErrorsIH shape
    exact Tree.CatalogSites.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenErrorsIH (shape.branches found form).1) (elseErrorsIH (shape.branches found form).2.1)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalog patternContext childErrors childErrorsIH shape
    exact Tree.CatalogSites.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued) catalog patternContext (fun request member childContext valid => childErrorsIH request member childContext valid (shape.match_request found form valid.forget))

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingLegacyCatalogSites
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
/-! Syntax weakening keeps the same prepared occurrences, keys and tokens.
The compiler certificates and original Source are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
open Core Frontend SourceInference
open GenericImperativeMatch
open PreparedBranchingCatalogSites
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
private theorem lexical_weaken {context mode statements expected}
    (tree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected) :
    GenericLexicalStatements.Syntax source (fun _ => True) context mode statements expected := by
  induction tree with
  | nil => apply GenericLexicalStatements.Syntax.nil <;> first | assumption | exact True.intro
  | returnUnit => apply GenericLexicalStatements.Syntax.returnUnit <;> first | assumption | exact True.intro
  | returnValue => apply GenericLexicalStatements.Syntax.returnValue <;> first | assumption | exact True.intro
  | tail => apply GenericLexicalStatements.Syntax.tail <;> first | assumption | exact True.intro
  | uninitialized => apply GenericLexicalStatements.Syntax.uninitialized <;> first | assumption | exact True.intro
  | initialized => apply GenericLexicalStatements.Syntax.initialized <;> first | assumption | exact True.intro
  | discard => apply GenericLexicalStatements.Syntax.discard <;> first | assumption | exact True.intro
  | block => apply GenericLexicalStatements.Syntax.block <;> first | assumption | exact True.intro
  | ifThen => apply GenericLexicalStatements.Syntax.ifThen <;> first | assumption | exact True.intro
  | terminalBlock => apply GenericLexicalStatements.Syntax.terminalBlock <;> first | assumption | exact True.intro
  | terminalIf => apply GenericLexicalStatements.Syntax.terminalIf <;> first | assumption | exact True.intro

private theorem weaken_all {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (sites : CatalogSites invalidProjection missingDefault registry faults tree) :
    ∃ tree : Tree layouts owner active frame globals onError values source (fun _ => True) certificates definitions administrative
      context scope position expected type code,
      CatalogSites invalidProjection missingDefault registry faults tree := by
  classical
  refine CatalogSites.rec (motive := fun {context scope position expected type code} _ _ =>
    ∃ tree : Tree layouts owner active frame globals onError values source (fun _ => True) certificates definitions administrative
      context scope position expected type code, CatalogSites invalidProjection missingDefault registry faults tree)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope mode statements expected type code syntaxTree body
    exact ⟨_, CatalogSites.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := lexical_weaken syntaxTree) (body := body)⟩
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨innerNew, innerSites⟩ := innerErrorsIH
    exact ⟨_, CatalogSites.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := innerNew) (remaining := remainingNew) (innerErrors := innerSites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨thenTreeNew, thenTreeSites⟩ := thenTreeErrorsIH
    obtain ⟨elseTreeNew, elseTreeSites⟩ := elseTreeErrorsIH
    exact ⟨_, CatalogSites.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTreeNew) (elseTree := elseTreeNew) (remaining := remainingNew) (thenTreeErrors := thenTreeSites) (elseTreeErrors := elseTreeSites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node rest expected type found form
    exact ⟨_, CatalogSites.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)⟩
  · intro context scope mode id node rest expected type found form
    exact ⟨_, CatalogSites.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)⟩
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨loopBodyNew, loopBodySites⟩ := loopBodyErrorsIH
    exact ⟨_, CatalogSites.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBodyNew) (nativeTyped := nativeTyped) (remaining := remainingNew) (loopBodyErrors := loopBodySites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.bitNotProjected (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    obtain ⟨initialNew, initialSites⟩ := initialErrorsIH
    exact ⟨_, CatalogSites.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initialNew) (remaining := remainingNew) (initialErrors := initialSites) (remainingErrors := remainingSites)⟩
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsIH
    obtain ⟨loopBodyNew, loopBodySites⟩ := loopErrorsIH
    exact ⟨_, CatalogSites.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBodyNew) (postTree := postTree) (nativeTyped := nativeTyped) (loopErrors := loopBodySites) (postErrors := postErrors)⟩
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remainingNew) (remainingErrors := remainingSites)⟩
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    exact ⟨_, CatalogSites.initializerBitNotProjected (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remainingNew) (remainingErrors := remainingSites) (headErrors := headErrors)⟩
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog patternContext childErrors remainingErrors childErrorsIH remainingErrorsIH
    obtain ⟨remainingNew, remainingSites⟩ := remainingErrorsIH
    let childrenNew := fun request member childContext valid => (childErrorsIH request member childContext valid).choose
    have childrenSites := fun request member childContext valid => (childErrorsIH request member childContext valid).choose_spec
    exact ⟨_, CatalogSites.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := childrenNew) (remaining := remainingNew) (catalog := catalog) (patternContext := patternContext) (childErrors := childrenSites) (remainingErrors := remainingSites)⟩
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerErrorsIH
    obtain ⟨innerNew, innerSites⟩ := innerErrorsIH
    exact ⟨_, CatalogSites.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := innerNew) (stops := stops) (issued := issued) (innerErrors := innerSites)⟩
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenErrorsIH elseErrorsIH
    obtain ⟨thenTreeNew, thenTreeSites⟩ := thenErrorsIH
    obtain ⟨elseTreeNew, elseTreeSites⟩ := elseErrorsIH
    exact ⟨_, CatalogSites.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTreeNew) (elseTree := elseTreeNew) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenErrors := thenTreeSites) (elseErrors := elseTreeSites)⟩
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalog patternContext childErrors childErrorsIH
    let childrenNew := fun request member childContext valid => (childErrorsIH request member childContext valid).choose
    have childrenSites := fun request member childContext valid => (childErrorsIH request member childContext valid).choose_spec
    exact ⟨_, CatalogSites.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := childrenNew) (stops := stops) (issued := issued) (catalog := catalog) (patternContext := patternContext) (childErrors := childrenSites)⟩

theorem weaken {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope mode statements expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code}
    (_unique : NodeOccurrencesUnique source)
    (sites : CatalogSites invalidProjection missingDefault registry faults tree) :
    ∃ tree : Tree layouts owner active frame globals onError values source (fun _ => True) certificates definitions administrative
      context scope (.statements mode statements) expected type code,
      CatalogSites invalidProjection missingDefault registry faults tree :=
  weaken_all sites

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLocalBindingOrigins
/-! Every native catalog binding retains its exact source declaration, even when
its instance bundle is empty. The witness comes from the actual preparation fold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalBindingOrigins
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

private theorem mapM_property {α β ε : Type} {items : List α} {values : List β}
    {action : α → Except ε β} {property : β → Prop}
    (accepted : items.mapM action = .ok values)
    (each : ∀ item ∈ items, ∀ value, action item = .ok value → property value) :
    ∀ value ∈ values, property value := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst values
    simp
  | cons item rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_ok accepted
    obtain ⟨tail, later, accepted⟩ := bind_ok accepted
    cases accepted
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact each item List.mem_cons_self _ first
    · exact ih later (fun next present => each next (List.mem_cons_of_mem item present)) value member

private theorem binding_mem {source : TypedSource} {statement : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : Node.statement statement ∈ source.nodes)
    (form : statement.form = .letDecl binder (some initializer))
    (quantified : binder.scheme.quantified.isEmpty = false)
    (direct : SourceSpecialization.isDirectLambdaInitializer source initializer = true) :
    ({ binder, initializer } : SourceSpecializationWorklist.LocalLambdaBinding) ∈
      SourceSpecializationWorklist.localLambdaBindings source := by
  change _ ∈ source.nodes.filterMap _
  apply List.mem_filterMap.mpr
  refine ⟨.statement statement, member, ?_⟩
  cases statement
  simp_all

def BindingOrigin (plan : SourceSpecializationWorklist.Plan) (binding : Binding) : Prop :=
  ∃ row ∈ plan.specializations,
    binding.caller = row.key ∧ binding.source = row.function.typedBody ∧
      ({ binder := binding.binder, initializer := binding.initializer } :
        SourceSpecializationWorklist.LocalLambdaBinding) ∈
          SourceSpecializationWorklist.localLambdaBindings binding.source

def CatalogOrigins (plan : SourceSpecializationWorklist.Plan) (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, BindingOrigin plan binding

theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogOrigins plan catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, _, accepted⟩ := bind_ok accepted
  obtain ⟨instances, _, accepted⟩ := bind_ok accepted
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, BindingOrigin plan binding
  apply forIn_invariant assembled (by simp)
  intro row rowMember before outcome previous iteration
  try dsimp only at iteration
  split at iteration
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at iteration
  · obtain ⟨after, nodes, iteration⟩ := bind_ok iteration
    cases iteration
    refine ⟨after, rfl, ?_⟩
    apply forIn_invariant nodes previous
    intro node nodeMember current outcome previous step
    try dsimp only at step
    split at step
    · split at step
      · cases step
        exact ⟨current, rfl, previous⟩
      · split at step
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at step
        · split at step
          · cases step
            refine ⟨_, rfl, ?_⟩
            intro binding member
            rcases List.mem_append.mp member with old | added
            · exact previous binding old
            · cases List.mem_singleton.mp added
              have collected := binding_mem nodeMember (by rfl) (by simp_all) (by assumption)
              exact ⟨row, rowMember, rfl, rfl, collected⟩
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {plan : SourceSpecializationWorklist.Plan} {catalog assigned : Catalog}
    {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (origins : CatalogOrigins plan catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogOrigins plan assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := BindingOrigin plan) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, _, actual⟩ := bind_ok actual
  cases actual
  exact origins binding member

theorem at_binding {plan : SourceSpecializationWorklist.Plan} {catalog : Catalog}
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    (origins : CatalogOrigins plan catalog)
    (located : catalog.binding caller binder = .ok binding) :
    BindingOrigin plan binding ∧ binding.caller = caller ∧ binding.binder.id = binder := by
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter
    (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have selected := List.mem_filter.mp (show binding ∈ catalog.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by
          rw [filtered]
          simp)
      exact ⟨origins binding selected.1, of_decide_eq_true selected.2⟩

theorem BindingOrigin.statement {plan : SourceSpecializationWorklist.Plan} {binding : Binding}
    (origin : BindingOrigin plan binding) :
    ∃ statement, Node.statement statement ∈ binding.source.nodes ∧
      statement.form = .letDecl binding.binder (some binding.initializer) := by
  obtain ⟨_, _, _, _, member⟩ := origin
  exact SourceSpecializationWorklist.localLambdaBindings_statement_origin member

end Solcore.SourceSemantics.CoreLowering.PreparedLocalBindingOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceOrigins
/-! Actual catalog generation identifies a contextual candidate with the
complete source binding that owns its bundle. Matching a local ID alone is
insufficient; the worklist's unique binding selection supplies the other fields. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceOrigins
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

private theorem mapM_property {α β ε : Type} {items : List α} {values : List β}
    {action : α → Except ε β} {property : β → Prop}
    (accepted : items.mapM action = .ok values)
    (each : ∀ item ∈ items, ∀ value, action item = .ok value → property value) :
    ∀ value ∈ values, property value := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst values
    simp
  | cons item rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_ok accepted
    obtain ⟨tail, later, accepted⟩ := bind_ok accepted
    cases accepted
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact each item List.mem_cons_self _ first
    · exact ih later (fun next present => each next (List.mem_cons_of_mem item present)) value member

private def unfoldAction (hypothesis : Lean.Name) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let some declaration := (← Lean.getLCtx).findFromUserName? hypothesis
      | throwError "missing accepted action"
    let type ← Lean.instantiateMVars (← Lean.Meta.inferType declaration.toExpr)
    let some (_, left, _) := type.eq? | throwError "expected equality"
    let .const action _ := left.getAppFn | throwError "expected compiler action"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let updated ← Lean.Meta.unfoldLocalDecl goal declaration.fvarId action
    Lean.Elab.Tactic.replaceMainGoal [updated]

private theorem checked_none {duplicate : Option (Key × Nat)}
    (accepted : (match duplicate with
      | none => Except.ok ()
      | some (key, count) => Except.error
        (SourceSpecializationWorklist.Error.duplicatePlanSpecializations key count)) = .ok ()) :
    duplicate = none := by
  cases duplicate with
  | none => rfl
  | some value => rcases value with ⟨key, count⟩; cases accepted

private theorem unique_keys {plan : SourceSpecializationWorklist.Plan}
    (accepted : SourceSpecializationWorklist.validatePlanSpecializationsUnique plan = .ok ()) :
    (plan.specializations.map (·.key)).Nodup := by
  rcases plan with ⟨seeds, entries, calls, references⟩
  induction entries with
  | nil => exact .nil
  | cons head rest ih =>
    unfold SourceSpecializationWorklist.validatePlanSpecializationsUnique at accepted
    have noDuplicate := checked_none accepted
    change (if (rest.filter (fun entry => decide (entry.key = head.key))).isEmpty then _
      else some (head.key, (rest.filter (fun entry => decide (entry.key = head.key))).length + 1)) = none at noDuplicate
    split at noDuplicate
    · have absent : head.key ∉ rest.map (·.key) := by
        have empty : rest.filter (fun entry => decide (entry.key = head.key)) = [] :=
          List.isEmpty_iff.mp ‹_ = true›
        intro member
        obtain ⟨entry, member, same⟩ := List.mem_map.mp member
        have : entry ∈ rest.filter (fun entry => decide (entry.key = head.key)) :=
          List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
        rw [empty] at this
        cases this
      have tailAccepted : SourceSpecializationWorklist.validatePlanSpecializationsUnique
          ⟨seeds, rest, calls, references⟩ = .ok () := by
        unfold SourceSpecializationWorklist.validatePlanSpecializationsUnique
        rw [noDuplicate]
        rfl
      exact List.nodup_cons.mpr ⟨absent, ih tailAccepted⟩
    · cases noDuplicate

private theorem same_key {rows : List SourceSpecialization.SpecializedFunction}
    (unique : (rows.map (·.key)).Nodup)
    {left right : SourceSpecialization.SpecializedFunction}
    (leftMember : left ∈ rows) (rightMember : right ∈ rows) (same : left.key = right.key) :
    left = right := by
  induction rows with
  | nil => cases leftMember
  | cons head tail ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · exact False.elim (absent (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact False.elim (absent (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih unique leftTail rightTail

def CatalogEntryOrigin (plan : SourceSpecializationWorklist.Plan)
    (entry : SourceCompilationPlan.LocalLambdaCatalogEntry) : Prop :=
  ∃ row ∈ plan.specializations,
    entry.caller = row.key ∧ entry.source = row.function.typedBody ∧
    SourceSpecializationWorklist.LocalLambdaBinding.Selected
      (SourceSpecializationWorklist.localLambdaBindings entry.source) entry.localInstance.binding

theorem catalog_entry_origins {plan : SourceSpecializationWorklist.Plan}
    {contextFuel : Option Nat} {entries : List SourceCompilationPlan.LocalLambdaCatalogEntry}
    (accepted : SourceCompilationPlan.localLambdaCatalog plan contextFuel = .ok entries) :
    (plan.specializations.map (·.key)).Nodup ∧
      ∀ entry ∈ entries, CatalogEntryOrigin plan entry := by
  unfold SourceCompilationPlan.localLambdaCatalog at accepted
  obtain ⟨done, validated, accepted⟩ := bind_ok accepted
  cases done
  obtain ⟨result, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  refine ⟨unique_keys validated, ?_⟩
  apply forIn_invariant assembled (by simp)
  intro row rowMember before outcome previous iteration
  obtain ⟨instances, discovered, iteration⟩ := bind_ok iteration
  obtain ⟨after, appended, iteration⟩ := bind_ok iteration
  cases iteration
  refine ⟨after, rfl, ?_⟩
  apply forIn_invariant appended previous
  intro localInstance present current outcome previous step
  obtain ⟨nodes, _, step⟩ := bind_ok step
  cases step
  refine ⟨_, rfl, ?_⟩
  intro entry occurs
  rcases List.mem_append.mp occurs with old | new
  · exact previous entry old
  · cases List.mem_singleton.mp new
    exact ⟨row, rowMember, rfl, rfl,
      SourceSpecializationWorklist.localLambdaInstances_selected discovered localInstance present⟩

private theorem binding_mem {source : TypedSource} {statement : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : Node.statement statement ∈ source.nodes)
    (form : statement.form = .letDecl binder (some initializer))
    (quantified : binder.scheme.quantified.isEmpty = false)
    (direct : SourceSpecialization.isDirectLambdaInitializer source initializer = true) :
    ({ binder, initializer } : SourceSpecializationWorklist.LocalLambdaBinding) ∈
      SourceSpecializationWorklist.localLambdaBindings source := by
  change _ ∈ source.nodes.filterMap _
  apply List.mem_filterMap.mpr
  refine ⟨.statement statement, member, ?_⟩
  cases statement
  simp_all

def BindingOrigins (binding : Binding) : Prop :=
  ∀ candidate ∈ binding.instances,
    candidate.origin.caller = binding.caller ∧
    candidate.origin.source = binding.source ∧
    candidate.origin.binder = binding.binder ∧
    candidate.origin.initializer = binding.initializer

def CatalogOrigins (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, BindingOrigins binding

private theorem candidate_binding {plan : SourceSpecializationWorklist.Plan}
    (unique : (plan.specializations.map (·.key)).Nodup)
    {candidate : Instance} (origin : CatalogEntryOrigin plan candidate.origin)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ plan.specializations)
    {binder : TypedBinder} {initializer : ExpressionId}
    (binding : ({ binder, initializer } : SourceSpecializationWorklist.LocalLambdaBinding) ∈
      SourceSpecializationWorklist.localLambdaBindings row.function.typedBody)
    (caller : candidate.origin.caller = row.key)
    (id : candidate.origin.binder.id = binder.id) :
    candidate.origin.source = row.function.typedBody ∧
      candidate.origin.binder = binder ∧ candidate.origin.initializer = initializer := by
  obtain ⟨actual, present, actualCaller, actualSource, selected⟩ := origin
  have same := same_key unique present member (actualCaller.symm.trans caller)
  subst actual
  have picked : ({ binder, initializer } : SourceSpecializationWorklist.LocalLambdaBinding) ∈
      (SourceSpecializationWorklist.localLambdaBindings candidate.origin.source).filter
        (fun entry => entry.binder.id == candidate.origin.binder.id) := by
    apply List.mem_filter.mpr
    exact ⟨actualSource.symm ▸ binding, by simp [id]⟩
  change _ = [candidate.origin.localInstance.binding] at selected
  simp only [SourceCompilationPlan.LocalLambdaCatalogEntry.binder] at picked
  rw [selected] at picked
  have sameBinding := List.mem_singleton.mp picked
  exact ⟨actualSource, (congrArg SourceSpecializationWorklist.LocalLambdaBinding.binder sameBinding).symm,
    (congrArg SourceSpecializationWorklist.LocalLambdaBinding.initializer sameBinding).symm⟩

theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogOrigins catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, discovered, accepted⟩ := bind_ok accepted
  have discovered : SourceCompilationPlan.localLambdaCatalog plan contextFuel = .ok entries := by
    cases actual : SourceCompilationPlan.localLambdaCatalog plan contextFuel <;> simp_all [Except.mapError]
  obtain ⟨unique, origins⟩ := catalog_entry_origins discovered
  obtain ⟨instances, prepared, accepted⟩ := bind_ok accepted
  have instancesOrigin : ∀ candidate ∈ instances, CatalogEntryOrigin plan candidate.origin := by
    refine mapM_property (property := fun candidate => CatalogEntryOrigin plan candidate.origin) prepared ?_
    intro entry member candidate actual
    have same : candidate.origin = entry := by
      run_tac unfoldAction `actual
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at actual
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      obtain ⟨_, _, actual⟩ := bind_ok actual
      obtain ⟨_, _, actual⟩ := bind_ok actual
      cases actual
      rfl
    rw [same]
    exact origins entry member
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, BindingOrigins binding
  apply forIn_invariant assembled (by simp)
  intro row rowMember before outcome previous iteration
  try dsimp only at iteration
  split at iteration
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at iteration
  · obtain ⟨after, nodes, iteration⟩ := bind_ok iteration
    cases iteration
    refine ⟨after, rfl, ?_⟩
    apply forIn_invariant nodes previous
    intro node nodeMember current outcome previous step
    try dsimp only at step
    split at step
    · split at step
      · cases step
        exact ⟨current, rfl, previous⟩
      · split at step
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at step
        · split at step
          · cases step
            refine ⟨_, rfl, ?_⟩
            intro binding member candidate candidateMember
            rcases List.mem_append.mp member with old | added
            · exact previous binding old candidate candidateMember
            · cases List.mem_singleton.mp added
              obtain ⟨present, picked⟩ := List.mem_filter.mp candidateMember
              have picked := of_decide_eq_true picked
              have collected := binding_mem nodeMember (by rfl) (by simp_all) (by assumption)
              exact ⟨picked.1, candidate_binding unique (instancesOrigin candidate present)
                rowMember collected picked.1 picked.2⟩
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {catalog assigned : Catalog}
    {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (origins : CatalogOrigins catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogOrigins assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := BindingOrigins) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, preparedInstances, actual⟩ := bind_ok actual
  cases actual
  refine mapM_property (property := fun candidate =>
    candidate.origin.caller = binding.caller ∧ candidate.origin.source = binding.source ∧
      candidate.origin.binder = binding.binder ∧ candidate.origin.initializer = binding.initializer)
    preparedInstances ?_
  intro candidate present decorated actual
  try dsimp only at actual
  split at actual <;> try contradiction
  cases actual
  exact origins binding member candidate present

theorem at_context {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} {active : Substitution} {candidate : Instance}
    (origins : CatalogOrigins catalog)
    (located : catalog.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    candidate.origin.caller = caller ∧ candidate.origin.source = binding.source ∧
      candidate.origin.binder = binding.binder ∧ candidate.origin.initializer = binding.initializer := by
  have instanceMember := (List.mem_filter.mp member).1
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter
    (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have selected := List.mem_filter.mp (show binding ∈ catalog.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by
          rw [filtered]
          simp)
      have identity := of_decide_eq_true selected.2
      have origin := origins binding selected.1 candidate instanceMember
      exact ⟨origin.1.trans identity.1, origin.2⟩

end Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceMetadata
/-! Successful local-instance preparation supplies the actual contextual lambda
and its checked native parameter and result types. Contract attachment changes
only the descriptor and keeps these facts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceMetadata
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

def Metadata (project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty) (candidate : Instance) : Prop :=
  candidate.source.owner = candidate.origin.caller.declaration ∧
  candidate.origin.binder.id.owner = candidate.source.owner ∧
  candidate.origin.initializer.occurrence.owner = candidate.source.owner ∧
  ∃ node parameters result body,
    candidate.source.lookupExpression? candidate.origin.initializer = some node ∧
    node.form = .lambda parameters result body ∧
    node.type = candidate.origin.substitution.apply candidate.origin.binder.scheme.body ∧
    node.type = .function (Ty.productMany (parameters.map (·.scheme.body))) result ∧
    node.type.freeVariables = [] ∧
    project (Ty.productMany (parameters.map (·.scheme.body))) = .ok candidate.parameterType ∧
    project result = .ok candidate.resultType

def BindingMetadata (project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty)
    (binding : Binding) : Prop :=
  ∀ candidate ∈ binding.instances,
    candidate.origin.caller = binding.caller ∧
    candidate.origin.binder.id = binding.binder.id ∧ Metadata project candidate

def CatalogMetadata (project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty) (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, BindingMetadata project binding

/-- Inspect the actual private compiler action and ask Lean to unfold it. No
generated private identifier or replacement implementation is used. -/
private def unfoldAction (hypothesis : Lean.Name) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let some declaration := (← Lean.getLCtx).findFromUserName? hypothesis
      | throwError "missing accepted action"
    let type ← Lean.instantiateMVars (← Lean.Meta.inferType declaration.toExpr)
    let some (_, left, _) := type.eq? | throwError "expected equality"
    let .const action _ := left.getAppFn | throwError "expected compiler action"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let updated ← Lean.Meta.unfoldLocalDecl goal declaration.fvarId action
    Lean.Elab.Tactic.replaceMainGoal [updated]

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapM_property {α β ε : Type} {items : List α} {values : List β}
    {action : α → Except ε β} {property : β → Prop}
    (accepted : items.mapM action = .ok values)
    (each : ∀ item ∈ items, ∀ value, action item = .ok value → property value) :
    ∀ value ∈ values, property value := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst values
    simp
  | cons item rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_ok accepted
    obtain ⟨tail, later, accepted⟩ := bind_ok accepted
    cases accepted
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact each item List.mem_cons_self _ first
    · exact ih later (fun next present => each next (List.mem_cons_of_mem item present)) value member

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

/-- The same preparation action authenticates every retained contextual lambda.
The final catalog loop only selects from that checked instance list. -/
theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogMetadata project catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, _, accepted⟩ := bind_ok accepted
  obtain ⟨instances, instantiated, accepted⟩ := bind_ok accepted
  have valid : ∀ candidate ∈ instances, Metadata project candidate := by
    refine mapM_property (property := Metadata project) instantiated ?_
    intro entry _ candidate actual
    run_tac unfoldAction `actual
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at actual
    split at actual <;> try contradiction
    split at actual <;> try contradiction
    split at actual <;> try contradiction
    split at actual <;> try contradiction
    split at actual <;> try contradiction
    split at actual <;> try contradiction
    split at actual <;> try contradiction
    split at actual <;> try contradiction
    obtain ⟨parameterType, projectedParameter, actual⟩ := bind_ok actual
    obtain ⟨resultType, projectedResult, actual⟩ := bind_ok actual
    cases actual
    simp_all [Metadata, Instance.source, Bool.or_eq_true, List.isEmpty_iff]
    refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    simp_all
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, BindingMetadata project binding
  apply forIn_invariant assembled (by simp)
  intro specialized _ before outcome previous iteration
  try dsimp only at iteration
  split at iteration
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at iteration
  · obtain ⟨after, nodes, iteration⟩ := bind_ok iteration
    cases iteration
    refine ⟨after, rfl, ?_⟩
    apply forIn_invariant nodes previous
    intro node _ current outcome previous step
    try dsimp only at step
    split at step
    · split at step
      · cases step
        exact ⟨current, rfl, previous⟩
      · split at step
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at step
        · split at step
          · cases step
            refine ⟨_, rfl, ?_⟩
            intro binding member candidate memberCandidate
            rcases List.mem_append.mp member with old | new
            · exact previous binding old candidate memberCandidate
            · cases List.mem_singleton.mp new
              obtain ⟨present, selected⟩ := List.mem_filter.mp memberCandidate
              have selected := of_decide_eq_true selected
              exact ⟨selected.1, selected.2, valid candidate present⟩
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {catalog assigned : Catalog} {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (valid : CatalogMetadata project catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogMetadata project assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := BindingMetadata project) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, preparedInstances, actual⟩ := bind_ok actual
  cases actual
  refine mapM_property (property := fun candidate =>
    candidate.origin.caller = binding.caller ∧
    candidate.origin.binder.id = binding.binder.id ∧ Metadata project candidate) preparedInstances ?_
  intro candidate present decorated actual
  try dsimp only at actual
  split at actual <;> try contradiction
  cases actual
  exact valid binding member candidate present

/-- A real binding lookup and lexical filter retain the authenticated instance;
the selection never substitutes a candidate from another caller or binder. -/
theorem at_context {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} {active : Substitution} {candidate : Instance}
    (valid : CatalogMetadata project catalog)
    (located : catalog.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    candidate.origin.caller = caller ∧ candidate.origin.binder.id = binder ∧
      Metadata project candidate := by
  have instanceMember := (List.mem_filter.mp member).1
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter
    (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have selected := List.mem_filter.mp (show binding ∈ catalog.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by
          rw [filtered]
          simp)
      have identity := of_decide_eq_true selected.2
      have metadata := valid binding selected.1 candidate instanceMember
      exact ⟨metadata.1.trans identity.1, metadata.2.1.trans identity.2, metadata.2.2⟩

end Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceMetadata
end
