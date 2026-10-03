import Solcore.SourceSemantics.CoreLowering.GenericImperativeForTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchMeaning

/-! Static inclusion keeps the existing imperative grammar and exact emitted
code. CatalogSites indexes that same Match Tree: catalog validity is required
only at a match site. For trees contain no such site, so their old meaning APIs
need no new catalog assumption. The receipt retains ReadyFor diagnostics together with site validity, so
child evidence is transported in one induction. No execution law is stored. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

namespace Tree
inductive CatalogSites (diagnosticPolicy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {position : Position} →
    {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code → Prop where
  | body {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code}
      : CatalogSites diagnosticPolicy registry faults (.body syntaxTree body)
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
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining)
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
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.discard found form notTail expressionFound value remaining)
  | block {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (innerErrors : CatalogSites diagnosticPolicy registry faults inner)
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.block found form inner remaining)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (thenTreeErrors : CatalogSites diagnosticPolicy registry faults thenTree)
      (elseTreeErrors : CatalogSites diagnosticPolicy registry faults elseTree)
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining)
  | breaking {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt}
      : CatalogSites diagnosticPolicy registry faults (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
  | continuing {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt}
      : CatalogSites diagnosticPolicy registry faults (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
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
      (loopBodyErrors : CatalogSites diagnosticPolicy registry faults loopBody)
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining)
  | assign {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      (headErrors : head.ErrorsFor diagnosticPolicy registry faults)
      : CatalogSites diagnosticPolicy registry faults (.assign found form head remaining)

  | bitNot {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      (headErrors : head.Errors faults)
      : CatalogSites diagnosticPolicy registry faults (.bitNot found form head remaining)

  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (initialErrors : CatalogSites diagnosticPolicy registry faults initial) (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining) :
      CatalogSites diagnosticPolicy registry faults (.forLoop found form initial remaining)
  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (loopErrors : CatalogSites diagnosticPolicy registry faults loopBody) (postErrors : GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree) :
      CatalogSites diagnosticPolicy registry faults (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped)
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
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining)
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
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      : CatalogSites diagnosticPolicy registry faults (.initializerDiscard found value remaining)
  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      (headErrors : head.ErrorsFor diagnosticPolicy registry faults)
      : CatalogSites diagnosticPolicy registry faults (.initializerAssign head remaining)
  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining)
      (headErrors : head.Errors faults)
      : CatalogSites diagnosticPolicy registry faults (.initializerBitNot head remaining)
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
      (patternContext : CompatiblePatternLeaves.ContextValid compilation context)
      (childErrors : ∀ request member childContext valid, CatalogSites diagnosticPolicy registry faults (children request member childContext valid))
      (remainingErrors : CatalogSites diagnosticPolicy registry faults remaining) :
      CatalogSites diagnosticPolicy registry faults (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children remaining)

  | terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type innerCode}
      {stops : GenericLexicalStatements.Stopped source statements}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (innerErrors : CatalogSites diagnosticPolicy registry faults inner) :
      CatalogSites diagnosticPolicy registry faults (.terminalBlock unique found form inner stops issued)
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
      (thenErrors : CatalogSites diagnosticPolicy registry faults thenTree)
      (elseErrors : CatalogSites diagnosticPolicy registry faults elseTree) :
      CatalogSites diagnosticPolicy registry faults
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
      (patternContext : CompatiblePatternLeaves.ContextValid compilation context)
      (childErrors : ∀ request member childContext valid, CatalogSites diagnosticPolicy registry faults (children request member childContext valid))
      :
      CatalogSites diagnosticPolicy registry faults (.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children stops issued)


theorem CatalogSites.of_catalog {policy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope position expected type code}
    (ready : ReadyFor policy registry faults tree) :
    CatalogSites policy registry faults tree := by
  induction ready
  case body => apply CatalogSites.body <;> assumption
  case uninitialized => apply CatalogSites.uninitialized <;> assumption
  case initialized => apply CatalogSites.initialized <;> assumption
  case discard => apply CatalogSites.discard <;> assumption
  case block => apply CatalogSites.block <;> assumption
  case ifThen => apply CatalogSites.ifThen <;> assumption
  case breaking => apply CatalogSites.breaking <;> assumption
  case continuing => apply CatalogSites.continuing <;> assumption
  case whileLoop => apply CatalogSites.whileLoop <;> assumption
  case assign => apply CatalogSites.assign <;> assumption
  case bitNot => apply CatalogSites.bitNot <;> assumption
  case forLoop => apply CatalogSites.forLoop <;> assumption
  case initializersDone => apply CatalogSites.initializersDone <;> assumption
  case initializerUninitialized => apply CatalogSites.initializerUninitialized <;> assumption
  case initializerInitialized => apply CatalogSites.initializerInitialized <;> assumption
  case initializerDiscard => apply CatalogSites.initializerDiscard <;> assumption
  case initializerAssign => apply CatalogSites.initializerAssign <;> assumption
  case initializerBitNot => apply CatalogSites.initializerBitNot <;> assumption
  case matchWith => apply CatalogSites.matchWith <;> assumption
  case terminalBlock => apply CatalogSites.terminalBlock <;> assumption
  case terminalIf => apply CatalogSites.terminalIf <;> assumption
  case terminalMatch => apply CatalogSites.terminalMatch <;> assumption

/-- The source positions, native code, administrative context and every static
child are preserved by inclusion. -/
theorem of_for     {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope position expected type code) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope position expected type code := by
  induction tree
  case body => apply Tree.body <;> assumption
  case uninitialized => apply Tree.uninitialized <;> assumption
  case initialized => apply Tree.initialized <;> assumption
  case discard => apply Tree.discard <;> assumption
  case block => apply Tree.block <;> assumption
  case ifThen => apply Tree.ifThen <;> assumption
  case breaking => apply Tree.breaking <;> assumption
  case continuing => apply Tree.continuing <;> assumption
  case whileLoop => apply Tree.whileLoop <;> assumption
  case assign => apply Tree.assign <;> assumption
  case bitNot => apply Tree.bitNot <;> assumption
  case forLoop => apply Tree.forLoop <;> assumption
  case initializersDone => apply Tree.initializersDone <;> assumption
  case initializerUninitialized => apply Tree.initializerUninitialized <;> assumption
  case initializerInitialized => apply Tree.initializerInitialized <;> assumption
  case initializerDiscard => apply Tree.initializerDiscard <;> assumption
  case initializerAssign => apply Tree.initializerAssign <;> assumption
  case initializerBitNot => apply Tree.initializerBitNot <;> assumption
  case terminalBlock => apply Tree.terminalBlock <;> assumption
  case terminalIf => apply Tree.terminalIf <;> assumption

/-- For inclusion needs only the original diagnostic evidence: it creates no
match node, and therefore needs no catalog validity assumption. -/
theorem CatalogSites.of_for {policy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope position expected type code}
    (errors : GenericImperativeFor.Tree.ErrorsFor policy registry faults tree) :
    CatalogSites policy registry faults (Tree.of_for tree) := by
  induction errors
  case body => apply CatalogSites.body <;> assumption
  case uninitialized => apply CatalogSites.uninitialized <;> assumption
  case initialized => apply CatalogSites.initialized <;> assumption
  case discard => apply CatalogSites.discard <;> assumption
  case block => apply CatalogSites.block <;> assumption
  case ifThen => apply CatalogSites.ifThen <;> assumption
  case breaking => apply CatalogSites.breaking <;> assumption
  case continuing => apply CatalogSites.continuing <;> assumption
  case whileLoop => apply CatalogSites.whileLoop <;> assumption
  case assign => apply CatalogSites.assign <;> assumption
  case bitNot => apply CatalogSites.bitNot <;> assumption
  case forLoop => apply CatalogSites.forLoop <;> assumption
  case initializersDone => apply CatalogSites.initializersDone <;> assumption
  case initializerUninitialized => apply CatalogSites.initializerUninitialized <;> assumption
  case initializerInitialized => apply CatalogSites.initializerInitialized <;> assumption
  case initializerDiscard => apply CatalogSites.initializerDiscard <;> assumption
  case initializerAssign => apply CatalogSites.initializerAssign <;> assumption
  case initializerBitNot => apply CatalogSites.initializerBitNot <;> assumption
  case terminalBlock => apply CatalogSites.terminalBlock <;> assumption
  case terminalIf => apply CatalogSites.terminalIf <;> assumption

/-- Erasing only site catalog evidence recovers the same ReadyFor receipt. -/
theorem CatalogSites.ready {policy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope position expected type code}
    (sites : CatalogSites policy registry faults tree) : ReadyFor policy registry faults tree := by
  induction sites
  case body => apply ReadyFor.body <;> assumption
  case uninitialized => apply ReadyFor.uninitialized <;> assumption
  case initialized => apply ReadyFor.initialized <;> assumption
  case discard => apply ReadyFor.discard <;> assumption
  case block => apply ReadyFor.block <;> assumption
  case ifThen => apply ReadyFor.ifThen <;> assumption
  case breaking => apply ReadyFor.breaking <;> assumption
  case continuing => apply ReadyFor.continuing <;> assumption
  case whileLoop => apply ReadyFor.whileLoop <;> assumption
  case assign => apply ReadyFor.assign <;> assumption
  case bitNot => apply ReadyFor.bitNot <;> assumption
  case forLoop => apply ReadyFor.forLoop <;> assumption
  case initializersDone => apply ReadyFor.initializersDone <;> assumption
  case initializerUninitialized => apply ReadyFor.initializerUninitialized <;> assumption
  case initializerInitialized => apply ReadyFor.initializerInitialized <;> assumption
  case initializerDiscard => apply ReadyFor.initializerDiscard <;> assumption
  case initializerAssign => apply ReadyFor.initializerAssign <;> assumption
  case initializerBitNot => apply ReadyFor.initializerBitNot <;> assumption
  case matchWith => apply ReadyFor.matchWith <;> assumption
  case terminalBlock => apply ReadyFor.terminalBlock <;> assumption
  case terminalIf => apply ReadyFor.terminalIf <;> assumption
  case terminalMatch => apply ReadyFor.terminalMatch <;> assumption

end Tree
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
