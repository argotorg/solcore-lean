import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaderTrees
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts

/-!
# Generic imperative matches: ready factories

Ready factory, extraction, prepared diagnostics and head bounds of imperative matches.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchReadyFactory
/-! The existing diagnostic receipt remains explicit. This positive receipt
adds only the fixed policy's ledger equality at each match site. A structural
fold reuses the source entry's context validity to construct pattern contexts;
no execution or child meaning is stored in the receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest)

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

/-- Match policy provenance on the same diagnostic tree. The index retains
all existing error laws; the only additional site fact is ledger equality. -/
inductive SiteLedgersFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (solved : List SolvedRequirement)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {position : Position} →
    {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code} → ErrorsFor diagnosticPolicy registry faults tree → Prop where
  | body
      {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code} :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode statements expected type code syntaxTree body)
  | uninitialized
      {context nextContext scope mode id node binder rest expected type body payload}
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
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors)
  | initialized
      {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
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
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors)
  | discard
      {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors)
  | block
      {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {innerErrors : ErrorsFor diagnosticPolicy registry faults inner}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (innerErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults innerErrors)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors)
  | ifThen
      {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {thenTreeErrors : ErrorsFor diagnosticPolicy registry faults thenTree}
      {elseTreeErrors : ErrorsFor diagnosticPolicy registry faults elseTree}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (thenTreeErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults thenTreeErrors)
      (elseTreeErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults elseTreeErrors)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors)
  | breaking
      {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt} :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form)
  | continuing
      {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt} :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form)
  | whileLoop
      {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
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
      {loopBodyErrors : ErrorsFor diagnosticPolicy registry faults loopBody}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (loopBodyErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults loopBodyErrors)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors)
  | assign
      {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (headErrors : head.ErrorsFor diagnosticPolicy registry faults)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors)
  | bitNot
      {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (headErrors : head.Errors faults)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors)
  | forLoop
      {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {initialErrors : ErrorsFor diagnosticPolicy registry faults initial}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (initialErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults initialErrors)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors)
  | initializersDone
      {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      {loopErrors : ErrorsFor diagnosticPolicy registry faults loopBody}
      (postErrors : GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
      (loopErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults loopErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors)
  | initializerUninitialized
      {context nextContext scope binder rest body payload condition post statements expected type}
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
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors)
  | initializerInitialized
      {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
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
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors)
  | initializerDiscard
      {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors)
  | initializerAssign
      {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (headErrors : head.ErrorsFor diagnosticPolicy registry faults)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors)
  | initializerBitNot
      {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (headErrors : head.Errors faults)
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors)
  | matchWith
      {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node}
      (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values}
      (sameDefinitions : compilation.definitions = definitions)
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
      {childErrors : ∀ request member childContext valid, ErrorsFor diagnosticPolicy registry faults (children request member childContext valid)}
      {remainingErrors : ErrorsFor diagnosticPolicy registry faults remaining}
      (sameLedger : compilation.solvedRequirements = solved)
      (childLedgers : ∀ request member childContext related, SiteLedgersFor diagnosticPolicy solved registry faults (childErrors request member childContext related))
      (remainingErrorsLedger : SiteLedgersFor diagnosticPolicy solved registry faults remainingErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childErrors remainingErrors)

  | terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type innerCode}
      {stops : GenericLexicalStatements.Stopped source statements}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      {innerErrors : ErrorsFor diagnosticPolicy registry faults inner}
      (innerLedger : SiteLedgersFor diagnosticPolicy solved registry faults innerErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults (ErrorsFor.terminalBlock (unique := unique) (found := found) (form := form) (stops := stops) (issued := issued) innerErrors)
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
      {thenErrors : ErrorsFor diagnosticPolicy registry faults thenTree}
      {elseErrors : ErrorsFor diagnosticPolicy registry faults elseTree}
      (thenLedger : SiteLedgersFor diagnosticPolicy solved registry faults thenErrors)
      (elseLedger : SiteLedgersFor diagnosticPolicy solved registry faults elseErrors) :
      SiteLedgersFor diagnosticPolicy solved registry faults
        (ErrorsFor.terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenErrors elseErrors)

  | terminalMatch
      {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node}
      (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values}
      (sameDefinitions : compilation.definitions = definitions)
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
      {childErrors : ∀ request member childContext valid, ErrorsFor diagnosticPolicy registry faults (children request member childContext valid)}
      (sameLedger : compilation.solvedRequirements = solved)
      (childLedgers : ∀ request member childContext related, SiteLedgersFor diagnosticPolicy solved registry faults (childErrors request member childContext related))
      :
      SiteLedgersFor diagnosticPolicy solved registry faults (@ErrorsFor.terminalMatch layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued childErrors)

/-- Original ledger receipt at the unconditional diagnostic specialization. -/
abbrev SiteLedgers (solved : List SolvedRequirement)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (errors : Errors registry faults tree) : Prop := SiteLedgersFor .unconditional solved registry faults errors

namespace SiteLedgers
variable {solved : List SolvedRequirement}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

abbrev body
      {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code} :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode statements expected type code syntaxTree body) :=
  @SiteLedgersFor.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode statements expected type code syntaxTree body

abbrev uninitialized
      {context nextContext scope mode id node binder rest expected type body payload}
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
      {remainingErrors : Errors registry faults remaining}
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors) :=
  @SiteLedgersFor.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsLedger

abbrev initialized
      {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
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
      {remainingErrors : Errors registry faults remaining}
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors) :=
  @SiteLedgersFor.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsLedger

abbrev discard
      {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {remainingErrors : Errors registry faults remaining}
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors) :=
  @SiteLedgersFor.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsLedger

abbrev block
      {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {innerErrors : Errors registry faults inner}
      {remainingErrors : Errors registry faults remaining}
      (innerErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults innerErrors)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors) :=
  @SiteLedgersFor.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsLedger remainingErrorsLedger

abbrev ifThen
      {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {thenTreeErrors : Errors registry faults thenTree}
      {elseTreeErrors : Errors registry faults elseTree}
      {remainingErrors : Errors registry faults remaining}
      (thenTreeErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults thenTreeErrors)
      (elseTreeErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults elseTreeErrors)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors) :=
  @SiteLedgersFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsLedger elseTreeErrorsLedger remainingErrorsLedger

abbrev breaking
      {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt} :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node rest expected type found form) :=
  @SiteLedgersFor.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node rest expected type found form

abbrev continuing
      {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt} :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node rest expected type found form) :=
  @SiteLedgersFor.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node rest expected type found form

abbrev whileLoop
      {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
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
      {loopBodyErrors : Errors registry faults loopBody}
      {remainingErrors : Errors registry faults remaining}
      (loopBodyErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults loopBodyErrors)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors) :=
  @SiteLedgersFor.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsLedger remainingErrorsLedger

abbrev assign
      {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {remainingErrors : Errors registry faults remaining}
      (headErrors : head.Errors registry faults)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors) :=
  @SiteLedgersFor.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsLedger

abbrev bitNot
      {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {remainingErrors : Errors registry faults remaining}
      (headErrors : head.Errors faults)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors) :=
  @SiteLedgersFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsLedger

abbrev forLoop
      {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {initialErrors : Errors registry faults initial}
      {remainingErrors : Errors registry faults remaining}
      (initialErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults initialErrors)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors) :=
  @SiteLedgersFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsLedger remainingErrorsLedger

abbrev initializersDone
      {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      {loopErrors : Errors registry faults loopBody}
      (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
      (loopErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults loopErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors) :=
  @SiteLedgersFor.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsLedger

abbrev initializerUninitialized
      {context nextContext scope binder rest body payload condition post statements expected type}
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
      {remainingErrors : Errors registry faults remaining}
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors) :=
  @SiteLedgersFor.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsLedger

abbrev initializerInitialized
      {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
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
      {remainingErrors : Errors registry faults remaining}
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors) :=
  @SiteLedgersFor.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsLedger

abbrev initializerDiscard
      {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingErrors : Errors registry faults remaining}
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors) :=
  @SiteLedgersFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsLedger

abbrev initializerAssign
      {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingErrors : Errors registry faults remaining}
      (headErrors : head.Errors registry faults)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors) :=
  @SiteLedgersFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsLedger

abbrev initializerBitNot
      {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingErrors : Errors registry faults remaining}
      (headErrors : head.Errors faults)
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors) :=
  @SiteLedgersFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsLedger

abbrev matchWith
      {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node}
      (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values}
      (sameDefinitions : compilation.definitions = definitions)
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
      {childErrors : ∀ request member childContext valid, Errors registry faults (children request member childContext valid)}
      {remainingErrors : Errors registry faults remaining}
      (sameLedger : compilation.solvedRequirements = solved)
      (childLedgers : ∀ request member childContext related, SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (childErrors request member childContext related))
      (remainingErrorsLedger : SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults remainingErrors) :
      SiteLedgers (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) solved registry faults (@Errors.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childErrors remainingErrors) :=
  @SiteLedgersFor.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional solved registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childErrors remainingErrors sameLedger childLedgers remainingErrorsLedger

end SiteLedgers

theorem SiteLedgersFor.ready {diagnosticPolicy : AssignmentDiagnosticPolicy} {solved : List SolvedRequirement}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    {errors : ErrorsFor diagnosticPolicy registry faults tree}
    (ledgers : SiteLedgersFor diagnosticPolicy solved registry faults errors) {evidence : Dynamic.EvidenceEnvironment} :
    CompatibleExpressionLiterals.ContextValid solved context evidence →
    context.signatures = values.checked.signatures → ReadyFor diagnosticPolicy registry faults tree := by
  induction ledgers with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro valid signatures
    exact @ReadyFor.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode statements expected type code syntaxTree body
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining (remainingErrorsIH (TypedLexicalControl.valid_extend valid extended) (extended.context_fields.1.trans signatures))
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining (remainingErrorsIH (TypedLexicalControl.valid_extend valid extended) (extended.context_fields.1.trans signatures))
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining (remainingErrorsIH valid signatures)
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsLedger remainingErrorsLedger innerErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining (innerErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsLedger elseTreeErrorsLedger remainingErrorsLedger thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining (thenTreeErrorsIH valid signatures) (elseTreeErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @breaking context scope mode id node rest expected type found form =>
    intro valid signatures
    exact @ReadyFor.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form
  | @continuing context scope mode id node rest expected type found form =>
    intro valid signatures
    exact @ReadyFor.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsLedger remainingErrorsLedger loopBodyErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining (loopBodyErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining (remainingErrorsIH valid signatures) headErrors
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment rest expected type body found form head remaining (remainingErrorsIH valid signatures) headErrors
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsLedger remainingErrorsLedger initialErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining (initialErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsLedger loopErrorsIH =>
    intro valid signatures
    exact @ReadyFor.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped (loopErrorsIH valid signatures) postErrors
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining (remainingErrorsIH (TypedLexicalControl.valid_extend valid extended) (extended.context_fields.1.trans signatures))
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining (remainingErrorsIH (TypedLexicalControl.valid_extend valid extended) (extended.context_fields.1.trans signatures))
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope expression expressionNode rest lowered body condition post statements expected type found value remaining (remainingErrorsIH valid signatures)
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining (remainingErrorsIH valid signatures) headErrors
  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment rest body condition post statements expected type head remaining (remainingErrorsIH valid signatures) headErrors
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childErrors remainingErrors sameLedger childLedgers remainingErrorsLedger childErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @ReadyFor.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining (CompatibleMatchContextFactory.of_context valid signatures sameValues sameLedger) (fun request member childContext related => childErrorsIH request member childContext related (CompatibleMatchContextFactory.scoped_context related valid) (related.closed_fields.1.trans signatures)) (remainingErrorsIH valid signatures)

  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerLedger innerIH =>
    intro valid signatures
    exact .terminalBlock (unique := unique) (found := found) (form := form) (stops := stops) (issued := issued) (innerIH valid signatures)
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenLedger elseLedger thenIH elseIH =>
    intro valid signatures
    exact .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenIH valid signatures) (elseIH valid signatures)

  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued childErrors sameLedger childLedgers childrenIH =>
    intro valid signatures
    exact @ReadyFor.terminalMatch layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued
      (CompatibleMatchContextFactory.of_context valid signatures sameValues sameLedger)
      (fun request member childContext related => childrenIH request member childContext related
        (CompatibleMatchContextFactory.scoped_context related valid) (related.closed_fields.1.trans signatures))

theorem SiteLedgers.ready {solved : List SolvedRequirement}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    {errors : Errors registry faults tree}
    (ledgers : SiteLedgers solved registry faults errors) {evidence : Dynamic.EvidenceEnvironment} :
    CompatibleExpressionLiterals.ContextValid solved context evidence →
    context.signatures = values.checked.signatures → Ready registry faults tree := by
  exact SiteLedgersFor.ready ledgers

end Tree
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchExtraction
/-! Static extraction results retain the actual recursive Tree and exactly the
per-site diagnostic obligations that it uses. Materializing those obligations
builds the existing Errors and SiteLedgers receipts. No source execution or
child semantic contract is stored in this factory. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest sequence)

structure Extraction (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) where
  tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
    context scope position expected type code
  diagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  materialize : ∀ registry faults, diagnostics registry faults →
    ∃ errors : Tree.Errors registry faults tree, Tree.SiteLedgers solved registry faults errors

structure ExtractionFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) where
  tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
    context scope position expected type code
  diagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  materialize : ∀ registry faults, diagnostics registry faults →
    ∃ errors : Tree.ErrorsFor diagnosticPolicy registry faults tree, Tree.SiteLedgersFor diagnosticPolicy solved registry faults errors

namespace Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement}

variable {context : SourceSemantics.Context} {scope : Scope} {position : Position}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

def to_for (receipt : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope position expected type code) :
    ExtractionFor .unconditional layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope position expected type code :=
  ⟨receipt.tree, receipt.diagnostics, receipt.materialize⟩
end Extraction
namespace ExtractionFor
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement}

variable {context : SourceSemantics.Context} {scope : Scope} {position : Position}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

def to_strict (receipt : ExtractionFor .unconditional layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope position expected type code) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope position expected type code :=
  ⟨receipt.tree, receipt.diagnostics, receipt.materialize⟩
end ExtractionFor

namespace ExtractionFor
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}

def body
    {context scope mode statements expected type code}
    (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
    (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode statements) expected type code := by
  refine ⟨(@Tree.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode statements expected type code syntaxTree body), (fun registry
    faults => True), ?_⟩
  intro registry faults provided
  exact ⟨@Tree.ErrorsFor.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode statements expected type code syntaxTree body,
    @Tree.SiteLedgersFor.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy solved registry faults context scope mode statements expected type code syntaxTree
    body⟩

def uninitialized
    {context nextContext scope mode id node binder rest expected type body payload}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  refine ⟨(@Tree.uninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope mode id node binder rest expected type body
    payload found form monomorphic extended ordinary projected allocation annotation same remaining.tree), (fun
    registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.uninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder rest
    expected type body payload found form monomorphic extended ordinary projected allocation annotation same
    remaining.tree remainingErrors, @Tree.SiteLedgersFor.uninitialized layouts owner active frame globals onError
    values source expressionSyntax certificates definitions administrative diagnosticPolicy solved registry faults context
    nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary
    projected allocation annotation same remaining.tree remainingErrors remainingErrorsLedger⟩

def initialized
    {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (initializerFound : source.lookupExpression? initializer = some initializerNode)
    (sourceType : initializerNode.type = binder.scheme.body)
    (initial : certificates context scope initializer lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨(@Tree.initialized layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context nextContext scope mode id node binder initializer initializerNode lowered
    body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation
    annotation same remaining.tree), (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.initialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder
    initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary
    initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors,
    @Tree.SiteLedgersFor.initialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy solved registry faults context nextContext scope mode id node binder
    initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary
    initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors
    remainingErrorsLedger⟩

def discard
    {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (expressionFound : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨(@Tree.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node expression expressionNode semicolon rest expected lowered
    type body found form notTail expressionFound value remaining.tree), (fun registry faults =>
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node expression expressionNode semicolon rest
    expected lowered type body found form notTail expressionFound value remaining.tree remainingErrors,
    @Tree.SiteLedgersFor.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy solved registry faults context scope mode id node expression expressionNode semicolon
    rest expected lowered type body found form notTail expressionFound value remaining.tree remainingErrors
    remainingErrorsLedger⟩

def block
    {context scope mode id node statements rest expected type innerCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type innerCode)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  refine ⟨(@Tree.block layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node statements rest expected type innerCode body found form
    inner.tree remaining.tree), (fun registry faults => inner.diagnostics registry faults ∧ remaining.diagnostics
    registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨innerErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨innerErrors, innerErrorsLedger⟩ := inner.materialize registry faults innerErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.block layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node statements rest expected type innerCode
    body found form inner.tree remaining.tree innerErrors remainingErrors, @Tree.SiteLedgersFor.block layouts owner
    active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy solved
    registry faults context scope mode id node statements rest expected type innerCode body found form inner.tree
    remaining.tree innerErrors remainingErrors innerErrorsLedger remainingErrorsLedger⟩

def ifThen
    {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false thenBody) expected type thenCode)
    (elseTree : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false (elseBody.getD [])) expected type elseCode)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  refine ⟨(@Tree.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node condition conditionNode thenBody elseBody rest expected
    type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree.tree
    elseTree.tree remaining.tree), (fun registry faults => thenTree.diagnostics registry faults ∧
    elseTree.diagnostics registry faults ∧ remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨thenTreeErrorsGiven, elseTreeErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨thenTreeErrors, thenTreeErrorsLedger⟩ := thenTree.materialize registry faults thenTreeErrorsGiven
  obtain ⟨elseTreeErrors, elseTreeErrorsLedger⟩ := elseTree.materialize registry faults elseTreeErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode thenBody elseBody
    rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree
    thenTree.tree elseTree.tree remaining.tree thenTreeErrors elseTreeErrors remainingErrors,
    @Tree.SiteLedgersFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy solved registry faults context scope mode id node condition conditionNode thenBody
    elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType
    conditionTree thenTree.tree elseTree.tree remaining.tree thenTreeErrors elseTreeErrors remainingErrors
    thenTreeErrorsLedger elseTreeErrorsLedger remainingErrorsLedger⟩

def breaking
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  refine ⟨(@Tree.breaking layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node rest expected type found form), (fun registry faults =>
    True), ?_⟩
  intro registry faults provided
  exact ⟨@Tree.ErrorsFor.breaking layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found
    form, @Tree.SiteLedgersFor.breaking layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy solved registry faults context scope mode id node rest expected type
    found form⟩

def continuing
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  refine ⟨(@Tree.continuing layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node rest expected type found form), (fun registry faults =>
    True), ?_⟩
  intro registry faults provided
  exact ⟨@Tree.ErrorsFor.continuing layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found
    form, @Tree.SiteLedgersFor.continuing layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy solved registry faults context scope mode id node rest expected type
    found form⟩

def whileLoop
    {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements false statements) expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  refine ⟨(@Tree.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node condition conditionNode statements rest expected type
    conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody.tree
    nativeTyped remaining.tree), (fun registry faults => loopBody.diagnostics registry faults ∧
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨loopBodyErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨loopBodyErrors, loopBodyErrorsLedger⟩ := loopBody.materialize registry faults loopBodyErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.whileLoop layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode
    statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType
    conditionTree loopBody.tree nativeTyped remaining.tree loopBodyErrors remainingErrors,
    @Tree.SiteLedgersFor.whileLoop layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy solved registry faults context scope mode id node condition
    conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound
    conditionType conditionTree loopBody.tree nativeTyped remaining.tree loopBodyErrors remainingErrors
    loopBodyErrorsLedger remainingErrorsLedger⟩

def assign
    {context scope mode id node assignment operator rhs rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.assign layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node assignment operator rhs rest expected type body found form
    head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.ErrorsFor diagnosticPolicy registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.assign layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node assignment operator rhs rest expected type
    body found form head remaining.tree remainingErrors headErrors, @Tree.SiteLedgersFor.assign layouts owner active
    frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy solved registry
    faults context scope mode id node assignment operator rhs rest expected type body found form head remaining.tree
    remainingErrors headErrors remainingErrorsLedger⟩

def bitNot
    {context scope mode id node assignment rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.bitNot layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node assignment rest expected type body found form head
    remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node assignment rest expected type body found
    form head remaining.tree remainingErrors headErrors, @Tree.SiteLedgersFor.bitNot layouts owner active frame globals
    onError values source expressionSyntax certificates definitions administrative diagnosticPolicy solved registry faults context
    scope mode id node assignment rest expected type body found form head remaining.tree remainingErrors headErrors
    remainingErrorsLedger⟩

def forLoop
    {context scope mode id node initializer condition post statements rest expected type initialCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post statements)
    (initial : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers initializer condition post statements) expected type initialCode)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  refine ⟨(@Tree.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node initializer condition post statements rest expected type
    initialCode body found form initial.tree remaining.tree), (fun registry faults => initial.diagnostics registry
    faults ∧ remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨initialErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨initialErrors, initialErrorsLedger⟩ := initial.materialize registry faults initialErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node initializer condition post statements rest
    expected type initialCode body found form initial.tree remaining.tree initialErrors remainingErrors,
    @Tree.SiteLedgersFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy solved registry faults context scope mode id node initializer condition post
    statements rest expected type initialCode body found form initial.tree remaining.tree initialErrors
    remainingErrors initialErrorsLedger remainingErrorsLedger⟩

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  refine ⟨(@Tree.initializersDone layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope condition conditionNode post statements expected type
    conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody.tree postTree
    nativeTyped), (fun registry faults => loopBody.diagnostics registry faults ∧ GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree), ?_⟩
  intro registry faults provided
  rcases provided with ⟨loopErrorsGiven, postErrors⟩
  obtain ⟨loopErrors, loopErrorsLedger⟩ := loopBody.materialize registry faults loopErrorsGiven
  exact ⟨@Tree.ErrorsFor.initializersDone layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope condition conditionNode post statements
    expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree
    loopBody.tree postTree nativeTyped loopErrors postErrors, @Tree.SiteLedgersFor.initializersDone layouts owner
    active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy solved
    registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode
    postCode selfReason conditionFound conditionType conditionTree loopBody.tree postTree nativeTyped loopErrors
    postErrors loopErrorsLedger⟩

def initializerUninitialized
    {context nextContext scope binder rest body payload condition post statements expected type}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  refine ⟨(@Tree.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope binder rest body payload condition post
    statements expected type monomorphic extended ordinary projected allocation annotation same remaining.tree),
    (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.initializerUninitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder rest
    body payload condition post statements expected type monomorphic extended ordinary projected allocation
    annotation same remaining.tree remainingErrors, @Tree.SiteLedgersFor.initializerUninitialized layouts owner active
    frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy solved registry
    faults context nextContext scope binder rest body payload condition post statements expected type monomorphic
    extended ordinary projected allocation annotation same remaining.tree remainingErrors remainingErrorsLedger⟩

def initializerInitialized
    {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (initializerFound : source.lookupExpression? initializer = some initializerNode)
    (sourceType : initializerNode.type = binder.scheme.body)
    (initial : certificates context scope initializer lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨(@Tree.initializerInitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope binder initializer initializerNode lowered
    body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType
    initial allocation annotation same remaining.tree), (fun registry faults => remaining.diagnostics registry
    faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.initializerInitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder
    initializer initializerNode lowered body rest condition post statements expected type monomorphic extended
    ordinary initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors,
    @Tree.SiteLedgersFor.initializerInitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative diagnosticPolicy solved registry faults context nextContext scope binder
    initializer initializerNode lowered body rest condition post statements expected type monomorphic extended
    ordinary initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors
    remainingErrorsLedger⟩

def initializerDiscard
    {context scope expression expressionNode rest lowered body condition post statements expected type}
    (found : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨(@Tree.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope expression expressionNode rest lowered body condition post
    statements expected type found value remaining.tree), (fun registry faults => remaining.diagnostics registry
    faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope expression expressionNode rest lowered
    body condition post statements expected type found value remaining.tree remainingErrors,
    @Tree.SiteLedgersFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy solved registry faults context scope expression expressionNode rest
    lowered body condition post statements expected type found value remaining.tree remainingErrors
    remainingErrorsLedger⟩

def initializerAssign
    {context scope assignment operator rhs rest body condition post statements expected type}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope assignment operator rhs rest body condition post
    statements expected type head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧
    head.ErrorsFor diagnosticPolicy registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope assignment operator rhs rest body
    condition post statements expected type head remaining.tree remainingErrors headErrors,
    @Tree.SiteLedgersFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy solved registry faults context scope assignment operator rhs rest body
    condition post statements expected type head remaining.tree remainingErrors headErrors remainingErrorsLedger⟩

def initializerBitNot
    {context scope assignment rest body condition post statements expected type}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.initializerBitNot layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope assignment rest body condition post statements expected
    type head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors faults),
    ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope assignment rest body condition post
    statements expected type head remaining.tree remainingErrors headErrors, @Tree.SiteLedgersFor.initializerBitNot
    layouts owner active frame globals onError values source expressionSyntax certificates definitions
    administrative diagnosticPolicy solved registry faults context scope assignment rest body condition post statements expected type
    head remaining.tree remainingErrors headErrors remainingErrorsLedger⟩

def matchWith
    {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    (compilation : SourceCoreCompatibleDataMatches.Context)
    (sameValues : compilation.values = values)
    (sameDefinitions : compilation.definitions = definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
    (requests : List GenericMatchChildren.Request)
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
    (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
          childContext request.scope (.statements false request.statements) expected type request.code)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body)
    (sameLedger : compilation.solvedRequirements = solved) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  refine ⟨(@Tree.matchWith layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node resolution scrutineeNode rest expected type matched body
    selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
    sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related =>
    (children request member childContext related).tree) remaining.tree), (fun registry faults => (∀ request member
    childContext related, (children request member childContext related).diagnostics registry faults) ∧
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨childErrorsGiven, remainingErrorsGiven⟩
  classical
  have childrenMaterialized := fun request member childContext related =>
    (children request member childContext related).materialize registry faults (childErrorsGiven request member childContext related)
  let childErrors := fun request member childContext related => Classical.choose (childrenMaterialized request member childContext related)
  have childLedgers := fun request member childContext related => Classical.choose_spec (childrenMaterialized request member childContext related)
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.ErrorsFor.matchWith layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest
    expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped
    defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member
    childContext related => (children request member childContext related).tree) remaining.tree childErrors
    remainingErrors, @Tree.SiteLedgersFor.matchWith layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative diagnosticPolicy solved registry faults context scope mode id node
    resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound
    scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt
    ordinary (fun request member childContext related => (children request member childContext related).tree)
    remaining.tree childErrors remainingErrors sameLedger childLedgers remainingErrorsLedger⟩

/-- Once the unchanged diagnostic obligations are interpreted, the actual
site ledgers and the caller's source context supply the existing Ready API. -/
theorem ready
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (extracted : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
      context scope position expected type code)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (diagnostics : extracted.diagnostics registry faults)
    {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.ReadyFor diagnosticPolicy registry faults extracted.tree := by
  obtain ⟨errors, ledgers⟩ := extracted.materialize registry faults diagnostics
  exact ledgers.ready valid signatures

end ExtractionFor

namespace Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement}

def body
    {context scope mode statements expected type code}
    (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
    (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode statements) expected type code := by
  exact (ExtractionFor.body (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)).to_strict

def uninitialized
    {context nextContext scope mode id node binder rest expected type body payload}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  exact (ExtractionFor.uninitialized (diagnosticPolicy := .unconditional) (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.to_for)).to_strict

def initialized
    {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (initializerFound : source.lookupExpression? initializer = some initializerNode)
    (sourceType : initializerNode.type = binder.scheme.body)
    (initial : certificates context scope initializer lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  exact (ExtractionFor.initialized (diagnosticPolicy := .unconditional) (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.to_for)).to_strict

def discard
    {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (expressionFound : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact (ExtractionFor.discard (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining.to_for)).to_strict

def block
    {context scope mode id node statements rest expected type innerCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type innerCode)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  exact (ExtractionFor.block (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner.to_for) (remaining := remaining.to_for)).to_strict

def ifThen
    {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false thenBody) expected type thenCode)
    (elseTree : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false (elseBody.getD [])) expected type elseCode)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  exact (ExtractionFor.ifThen (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.to_for) (elseTree := elseTree.to_for) (remaining := remaining.to_for)).to_strict

def breaking
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  exact (ExtractionFor.breaking (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)).to_strict

def continuing
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  exact (ExtractionFor.continuing (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)).to_strict

def whileLoop
    {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements false statements) expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  exact (ExtractionFor.whileLoop (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody.to_for) (nativeTyped := nativeTyped) (remaining := remaining.to_for)).to_strict

def assign
    {context scope mode id node assignment operator rhs rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact (ExtractionFor.assign (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining.to_for)).to_strict

def bitNot
    {context scope mode id node assignment rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact (ExtractionFor.bitNot (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining.to_for)).to_strict

def forLoop
    {context scope mode id node initializer condition post statements rest expected type initialCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post statements)
    (initial : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers initializer condition post statements) expected type initialCode)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  exact (ExtractionFor.forLoop (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial.to_for) (remaining := remaining.to_for)).to_strict

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  exact (ExtractionFor.initializersDone (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody.to_for) (postTree := postTree) (nativeTyped := nativeTyped)).to_strict

def initializerUninitialized
    {context nextContext scope binder rest body payload condition post statements expected type}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  exact (ExtractionFor.initializerUninitialized (diagnosticPolicy := .unconditional) (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.to_for)).to_strict

def initializerInitialized
    {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (initializerFound : source.lookupExpression? initializer = some initializerNode)
    (sourceType : initializerNode.type = binder.scheme.body)
    (initial : certificates context scope initializer lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  exact (ExtractionFor.initializerInitialized (diagnosticPolicy := .unconditional) (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.to_for)).to_strict

def initializerDiscard
    {context scope expression expressionNode rest lowered body condition post statements expected type}
    (found : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact (ExtractionFor.initializerDiscard (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining.to_for)).to_strict

def initializerAssign
    {context scope assignment operator rhs rest body condition post statements expected type}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact (ExtractionFor.initializerAssign (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining.to_for)).to_strict

def initializerBitNot
    {context scope assignment rest body condition post statements expected type}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact (ExtractionFor.initializerBitNot (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining.to_for)).to_strict

def matchWith
    {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    (compilation : SourceCoreCompatibleDataMatches.Context)
    (sameValues : compilation.values = values)
    (sameDefinitions : compilation.definitions = definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
    (requests : List GenericMatchChildren.Request)
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
    (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
          childContext request.scope (.statements false request.statements) expected type request.code)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body)
    (sameLedger : compilation.solvedRequirements = solved) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  exact (ExtractionFor.matchWith (diagnosticPolicy := .unconditional) (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := (fun request member childContext related => (children request member childContext related).to_for)) (remaining := remaining.to_for) (sameLedger := sameLedger)).to_strict

theorem ready
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (extracted : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
      context scope position expected type code)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (diagnostics : extracted.diagnostics registry faults)
    {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.Ready registry faults extracted.tree := by
  exact ExtractionFor.ready (context := context) (scope := scope) (position := position) (expected := expected) (type := type) (code := code) (extracted := extracted.to_for) (registry := registry) (faults := faults) (diagnostics := diagnostics) (evidence := evidence) (valid := valid) (signatures := signatures)

end Extraction
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchPreparedDiagnostics
/-! Diagnostic adapters for the existing extraction records. Only the local
operand obligation changes; materialization uses the original Errors and
SiteLedgers constructors on the same Tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
namespace PreparedDiagnostics
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}

def assign
    {context scope mode id node assignment operator rhs rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (headDiagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    (headErrors : ∀ registry faults, headDiagnostics registry faults → head.ErrorsFor diagnosticPolicy registry faults)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  let original := ExtractionFor.assign found form head remaining
  exact ⟨original.tree, (fun registry faults => remaining.diagnostics registry faults ∧ headDiagnostics registry faults),
    fun registry faults given => original.materialize registry faults ⟨given.1, headErrors registry faults given.2⟩⟩

def initializerAssign
    {context scope assignment operator rhs rest body condition post statements expected type}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (headDiagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    (headErrors : ∀ registry faults, headDiagnostics registry faults → head.ErrorsFor diagnosticPolicy registry faults)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  let original := ExtractionFor.initializerAssign head remaining
  exact ⟨original.tree, (fun registry faults => remaining.diagnostics registry faults ∧ headDiagnostics registry faults),
    fun registry faults given => original.materialize registry faults ⟨given.1, headErrors registry faults given.2⟩⟩

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  let original := ExtractionFor.initializersDone conditionFound conditionType conditionTree loopBody postTree.tree nativeTyped
  exact ⟨original.tree, (fun registry faults => loopBody.diagnostics registry faults ∧ postTree.diagnostics registry faults),
    fun registry faults given => original.materialize registry faults ⟨given.1, postTree.materialize registry faults given.2⟩⟩

end PreparedDiagnostics
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds
/-! Protected finite match heads consume only smaller expression and selected
body contracts. The original source and Core budgets remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ selected => exact default_selected selected
termination_by cases.length

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
  {program : Program} {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (valid : CompatiblePatternLeaves.ContextValid compilation context)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
  {solved : List SolvedRequirement} {administrative : Core.Context} {faults : FunctionCalls.FaultRep}

include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped in
/-- Concrete child induction discharges both selected-arm and default semantics.
The only expression is the singleton extracted from this actual receipt. -/
theorem head_preserves_bounded (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (solved := solved) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Head.HeadPreservesAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
      (context := context) (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  obtain ⟨lowered, child, restricted⟩ := Certificate.singleton receipt
  apply CompatibleMatchPreservation.Certificate.preserves_bounded onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique valid catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same) budget size bounded transport entryBindings
  · intro contextValid childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact expressionMeaning contextValid childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact children ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact children ⟨_, statements, body⟩ certified context (.default (default_selected selected) scopeIds)

include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped in
/-- Concrete child induction discharges both selected-arm and default semantics.
The only expression is the singleton extracted from this actual receipt. -/
theorem head_reflects_bounded (budget size : Nat) (bounded : size ≤ budget) {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (entryBindings : ProtectedExpressionMeaning.Binds entry)
    (expressionMeaning : CompatibleExpressionLiterals.ContextValid solved context evidence →
      ∀ child, child < budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        program context evidence source expressionCertificate faults entry)
    (children : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
      ∀ child, child < budget → RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
        (context := childContext) (registry := registry) (solved := solved) (administrative := administrative)
        (frameLayout := frame) (globals := globals) (faults := faults) (scope := request.scope)
        child false request.statements expected type request.code) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAt (entry := entry) functions program evidence (values := compilation.values) (source := source)
      (context := context) (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults) size (scope := scope) id expected type code := by
  obtain ⟨lowered, child, restricted⟩ := Certificate.singleton receipt
  apply CompatibleMatchReflection.Certificate.reflects_bounded onError allocator functions definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) valid catalogValid found
    (fun _ certificate => certificate.2.2) casesTyped (fun same => defaultTyped _ same) budget size bounded transport entryBindings
  · intro contextValid childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact expressionMeaning contextValid childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact children ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact children ⟨_, statements, body⟩ certified context (.default (default_selected selected) scopeIds)


end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end
