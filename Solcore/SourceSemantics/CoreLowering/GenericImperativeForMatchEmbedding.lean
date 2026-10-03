import Solcore.SourceSemantics.CoreLowering.GenericImperativeForTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchContextFactory

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
/-- Match metadata names the same full signature and solved-row lists. Whether
those rows are ordinary or runtime-valid is supplied at the reached context. -/
structure MatchContextFields (compilation : SourceCoreCompatibleDataMatches.Context)
    (context : SourceSemantics.Context) : Prop where
  signatures : context.signatures = compilation.signatures
  ledger : context.solvedRequirements = compilation.solvedRequirements

theorem MatchContextFields.of_ordinary
    {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    (valid : CompatiblePatternLeaves.ContextValid compilation context) :
    MatchContextFields compilation context := ⟨valid.signatures, valid.ledger⟩

theorem MatchContextFields.ordinary
    {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    (fields : MatchContextFields compilation context)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) :
    CompatiblePatternLeaves.ContextValid compilation context :=
  ⟨fields.signatures, fields.ledger, valid.valid⟩

theorem MatchContextFields.runtime
    {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    (fields : MatchContextFields compilation context)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence) :
    CompatiblePatternRuntime.ContextValid compilation context :=
  ⟨fields.signatures, fields.ledger, valid.runtime⟩

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
      (patternContext : MatchContextFields compilation context)
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
      (patternContext : MatchContextFields compilation context)
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
  case matchWith => apply CatalogSites.matchWith <;> first | assumption | exact MatchContextFields.of_ordinary (by assumption)
  case terminalBlock => apply CatalogSites.terminalBlock <;> assumption
  case terminalIf => apply CatalogSites.terminalIf <;> assumption
  case terminalMatch => apply CatalogSites.terminalMatch <;> first | assumption | exact MatchContextFields.of_ordinary (by assumption)

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

/-- Ordinary readiness additionally requires the actual root ordinary context.
The same binder and selected-arm relations transport it to each match site. -/
theorem CatalogSites.ready {policy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope position expected type code}
    (sites : CatalogSites policy registry faults tree)
    {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) : ReadyFor policy registry faults tree := by
  revert valid
  induction sites with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro valid
    exact ReadyFor.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected)
      (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id)
      (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type)
      (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic)
      (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation)
      (same := same) (remaining := remaining) (remainingErrors := remainingErrors_ih (TypedLexicalControl.valid_extend valid extended))
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id)
      (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered)
      (body := body) (rest := rest) (expected := expected) (type := type) (found := found)
      (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound)
      (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same)
      (remaining := remaining) (remainingErrors := remainingErrors_ih (TypedLexicalControl.valid_extend valid extended))
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected)
      (lowered := lowered) (type := type) (body := body) (found := found) (form := form)
      (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining) (remainingErrors := remainingErrors_ih valid)
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrors_ih remainingErrors_ih =>
    intro valid
    exact ReadyFor.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode)
      (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining)
      (innerErrors := innerErrors_ih valid) (remainingErrors := remainingErrors_ih valid)
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrors_ih elseTreeErrors_ih remainingErrors_ih =>
    intro valid
    exact ReadyFor.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest)
      (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode)
      (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType)
      (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining) (thenTreeErrors := thenTreeErrors_ih valid)
      (elseTreeErrors := elseTreeErrors_ih valid) (remainingErrors := remainingErrors_ih valid)
  | @breaking context scope mode id node rest expected type found form =>
    intro valid
    exact ReadyFor.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  | @continuing context scope mode id node rest expected type found form =>
    intro valid
    exact ReadyFor.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrors_ih remainingErrors_ih =>
    intro valid
    exact ReadyFor.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected)
      (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason)
      (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
      (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining) (loopBodyErrors := loopBodyErrors_ih valid) (remainingErrors := remainingErrors_ih valid)
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected)
      (type := type) (body := body) (found := found) (form := form) (head := head)
      (remaining := remaining) (remainingErrors := remainingErrors_ih valid) (headErrors := headErrors)
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body)
      (found := found) (form := form) (head := head) (remaining := remaining) (remainingErrors := remainingErrors_ih valid)
      (headErrors := headErrors)
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrors_ih remainingErrors_ih =>
    intro valid
    exact ReadyFor.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest)
      (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found)
      (form := form) (initial := initial) (remaining := remaining) (initialErrors := initialErrors_ih valid) (remainingErrors := remainingErrors_ih valid)
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrors_ih =>
    intro valid
    exact ReadyFor.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post)
      (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode)
      (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
      (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped) (loopErrors := loopErrors_ih valid) (postErrors := postErrors)
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest)
      (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements)
      (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary)
      (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
      (remainingErrors := remainingErrors_ih (TypedLexicalControl.valid_extend valid extended))
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer)
      (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition)
      (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic)
      (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial)
      (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (remainingErrors := remainingErrors_ih (TypedLexicalControl.valid_extend valid extended))
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest)
      (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements)
      (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining)
      (remainingErrors := remainingErrors_ih valid)
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs)
      (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements)
      (expected := expected) (type := type) (head := head) (remaining := remaining) (remainingErrors := remainingErrors_ih valid)
      (headErrors := headErrors)
  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrors_ih =>
    intro valid
    exact ReadyFor.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body)
      (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type)
      (head := head) (remaining := remaining) (remainingErrors := remainingErrors_ih valid) (headErrors := headErrors)
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog patternContext childErrors remainingErrors childErrors_ih remainingErrors_ih =>
    intro valid
    exact ReadyFor.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type)
      (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts)
      (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped)
      (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator)
      (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining)
      (patternContext := patternContext.ordinary valid) (childErrors := fun request member childContext related => childErrors_ih request member childContext related (CompatibleMatchContextFactory.scoped_context related valid)) (remainingErrors := remainingErrors_ih valid)
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerErrors_ih =>
    intro valid
    exact ReadyFor.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode)
      (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner)
      (stops := stops) (issued := issued) (innerErrors := innerErrors_ih valid)
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenErrors_ih elseErrors_ih =>
    intro valid
    exact ReadyFor.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest)
      (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode)
      (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound)
      (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops)
      (elseStops := elseStops) (issued := issued) (thenErrors := thenErrors_ih valid) (elseErrors := elseErrors_ih valid)
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalog patternContext childErrors childErrors_ih =>
    intro valid
    exact ReadyFor.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node)
      (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type)
      (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts)
      (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped)
      (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions)
      (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children)
      (stops := stops) (issued := issued) (patternContext := patternContext.ordinary valid) (childErrors := fun request member childContext related => childErrors_ih request member childContext related (CompatibleMatchContextFactory.scoped_context related valid))

end Tree
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
