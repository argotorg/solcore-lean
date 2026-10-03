import Solcore.SourceSemantics.CoreLowering.CompatibleMatchContextFactory
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchMeaning

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
