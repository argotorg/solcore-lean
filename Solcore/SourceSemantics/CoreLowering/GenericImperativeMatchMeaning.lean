import Solcore.SourceSemantics.CoreLowering.GenericImperativeWhileComposition
import Solcore.SourceSemantics.CoreLowering.GenericImperativeWhileReflection
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchControlShape
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeads
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForInitializers
import Solcore.SourceSemantics.CoreLowering.GenericImperativeAssignment

/-! Finite preservation and completed reflection for assignments, while/for
loops, lexical bindings, scoped control and actual compatible match branches. Concrete expression and statement
trees discharge every child meaning. Native typing is a separate static receipt;
scoped exits restore the source context while retaining effects and live cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof
open TypedScopedStatements (Executes)
open GenericImperative (assignment_preserves assignment_reflects assignment_preserves_reachable assignment_reflects_reachable)
open GenericImperativeWhile (conditional_preserves conditional_reflects while_preserves while_reflects)
open TypedLexicalWhile hiding Syntax Tree Scope ValuesContext absentRequest initializedRequest sequence conditional_preserves conditional_reflects while_preserves while_reflects
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized allocate_absent allocate_initialized sequence_rename valid_extend)

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}

/-- Static diagnostics and pattern contexts at the same recursive sites. -/
inductive ReadyFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {position : Position} →
    {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code → Prop where
  | body {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code}
      : ReadyFor diagnosticPolicy registry faults (.body syntaxTree body)
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
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining)
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
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.discard found form notTail expressionFound value remaining)
  | block {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (innerErrors : ReadyFor diagnosticPolicy registry faults inner)
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.block found form inner remaining)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (thenTreeErrors : ReadyFor diagnosticPolicy registry faults thenTree)
      (elseTreeErrors : ReadyFor diagnosticPolicy registry faults elseTree)
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining)
  | breaking {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt}
      : ReadyFor diagnosticPolicy registry faults (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
  | continuing {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt}
      : ReadyFor diagnosticPolicy registry faults (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
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
      (loopBodyErrors : ReadyFor diagnosticPolicy registry faults loopBody)
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining)
  | assign {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      (headErrors : head.ErrorsFor diagnosticPolicy registry faults)
      : ReadyFor diagnosticPolicy registry faults (.assign found form head remaining)

  | bitNot {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      (headErrors : head.Errors faults)
      : ReadyFor diagnosticPolicy registry faults (.bitNot found form head remaining)

  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (initialErrors : ReadyFor diagnosticPolicy registry faults initial) (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining) :
      ReadyFor diagnosticPolicy registry faults (.forLoop found form initial remaining)
  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (loopErrors : ReadyFor diagnosticPolicy registry faults loopBody) (postErrors : GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree) :
      ReadyFor diagnosticPolicy registry faults (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped)
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
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining)
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
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      : ReadyFor diagnosticPolicy registry faults (.initializerDiscard found value remaining)
  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      (headErrors : head.ErrorsFor diagnosticPolicy registry faults)
      : ReadyFor diagnosticPolicy registry faults (.initializerAssign head remaining)
  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining)
      (headErrors : head.Errors faults)
      : ReadyFor diagnosticPolicy registry faults (.initializerBitNot head remaining)
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
      (patternContext : CompatiblePatternLeaves.ContextValid compilation context)
      (childErrors : ∀ request member childContext valid, ReadyFor diagnosticPolicy registry faults (children request member childContext valid))
      (remainingErrors : ReadyFor diagnosticPolicy registry faults remaining) :
      ReadyFor diagnosticPolicy registry faults (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children remaining)

  | terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type innerCode}
      {stops : GenericLexicalStatements.Stopped source statements}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (innerErrors : ReadyFor diagnosticPolicy registry faults inner) :
      ReadyFor diagnosticPolicy registry faults (.terminalBlock unique found form inner stops issued)
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
      (thenErrors : ReadyFor diagnosticPolicy registry faults thenTree)
      (elseErrors : ReadyFor diagnosticPolicy registry faults elseTree) :
      ReadyFor diagnosticPolicy registry faults
        (.terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)

/-- The original receipt selects unconditional assignment diagnostics. -/
abbrev Ready (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code) : Prop := ReadyFor .unconditional registry faults tree

/-- Operand diagnostics are required only for independently derived failures. -/
abbrev ReachableReady (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code) : Prop := ReadyFor .reachable registry faults tree

namespace Ready
variable {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

abbrev body {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code}
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.body syntaxTree body) :=
  @ReadyFor.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode statements expected type code syntaxTree body

abbrev uninitialized {context nextContext scope mode id node binder rest expected type body payload}
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
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining) :=
  @ReadyFor.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors

abbrev initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
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
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining) :=
  @ReadyFor.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors

abbrev discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.discard found form notTail expressionFound value remaining) :=
  @ReadyFor.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors

abbrev block {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (innerErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults inner)
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.block found form inner remaining) :=
  @ReadyFor.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors

abbrev ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (thenTreeErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults thenTree)
      (elseTreeErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults elseTree)
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining) :=
  @ReadyFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors

abbrev breaking {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt}
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form) :=
  @ReadyFor.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node rest expected type found form

abbrev continuing {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt}
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form) :=
  @ReadyFor.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node rest expected type found form

abbrev whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
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
      (loopBodyErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults loopBody)
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining) :=
  @ReadyFor.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors

abbrev assign {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.assign found form head remaining) :=
  @ReadyFor.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors

abbrev bitNot {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      (headErrors : head.Errors faults)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.bitNot found form head remaining) :=
  @ReadyFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors

abbrev forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (initialErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults initial) (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining) :
      Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.forLoop found form initial remaining) :=
  @ReadyFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors

abbrev initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (loopErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults loopBody) (postErrors : GenericForHeader.Tree.Errors registry faults postTree) :
      Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped) :=
  @ReadyFor.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors

abbrev initializerUninitialized {context nextContext scope binder rest body payload condition post statements expected type}
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
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining) :=
  @ReadyFor.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors

abbrev initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
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
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining) :=
  @ReadyFor.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors

abbrev initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.initializerDiscard found value remaining) :=
  @ReadyFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors

abbrev initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.initializerAssign head remaining) :=
  @ReadyFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors

abbrev initializerBitNot {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining)
      (headErrors : head.Errors faults)
      : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.initializerBitNot head remaining) :=
  @ReadyFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors

abbrev matchWith {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
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
      (patternContext : CompatiblePatternLeaves.ContextValid compilation context)
      (childErrors : ∀ request member childContext valid, Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (children request member childContext valid))
      (remainingErrors : Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults remaining) :
      Ready (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) registry faults (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children remaining) :=
  @ReadyFor.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .unconditional registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining patternContext childErrors remainingErrors

end Ready

theorem ReadyFor.reachable {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (receipt : ReadyFor diagnosticPolicy registry faults tree) : ReachableReady registry faults tree := by
  induction receipt with
  | @body context scope mode statements expected type code syntaxTree body =>
    exact @ReadyFor.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode statements expected type code syntaxTree body
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors ih_remainingErrors =>
    exact @ReadyFor.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining ih_remainingErrors
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors ih_remainingErrors =>
    exact @ReadyFor.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining ih_remainingErrors
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors ih_remainingErrors =>
    exact @ReadyFor.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih_remainingErrors
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors ih_innerErrors ih_remainingErrors =>
    exact @ReadyFor.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining ih_innerErrors ih_remainingErrors
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors ih_thenTreeErrors ih_elseTreeErrors ih_remainingErrors =>
    exact @ReadyFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining ih_thenTreeErrors ih_elseTreeErrors ih_remainingErrors
  | @breaking context scope mode id node rest expected type found form =>
    exact @ReadyFor.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node rest expected type found form
  | @continuing context scope mode id node rest expected type found form =>
    exact @ReadyFor.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node rest expected type found form
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors ih_loopBodyErrors ih_remainingErrors =>
    exact @ReadyFor.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining ih_loopBodyErrors ih_remainingErrors
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih_remainingErrors =>
    exact @ReadyFor.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining ih_remainingErrors (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors)
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih_remainingErrors =>
    exact @ReadyFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node assignment rest expected type body found form head remaining ih_remainingErrors headErrors
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors ih_initialErrors ih_remainingErrors =>
    exact @ReadyFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining ih_initialErrors ih_remainingErrors
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors ih_loopErrors =>
    exact @ReadyFor.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped ih_loopErrors (GenericForHeader.Tree.ErrorsFor.reachable postErrors)
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors ih_remainingErrors =>
    exact @ReadyFor.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining ih_remainingErrors
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors ih_remainingErrors =>
    exact @ReadyFor.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining ih_remainingErrors
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors ih_remainingErrors =>
    exact @ReadyFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope expression expressionNode rest lowered body condition post statements expected type found value remaining ih_remainingErrors
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih_remainingErrors =>
    exact @ReadyFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining ih_remainingErrors (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors)
  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih_remainingErrors =>
    exact @ReadyFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope assignment rest body condition post statements expected type head remaining ih_remainingErrors headErrors
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining patternContext childErrors remainingErrors ih_childErrors ih_remainingErrors =>
    exact @ReadyFor.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative .reachable registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining patternContext ih_childErrors ih_remainingErrors


  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerIH =>
    exact .terminalBlock (unique := unique) (found := found) (form := form) (stops := stops) (issued := issued) innerIH
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    exact .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenIH elseIH

/-- Discarding pattern-context receipts recovers the original diagnostics tree. -/
theorem ReadyFor.errors {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (ready : ReadyFor diagnosticPolicy registry faults tree) : ErrorsFor diagnosticPolicy registry faults tree := by
  induction ready with
  | @body context scope mode statements expected type code syntaxTree body => exact @ErrorsFor.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode statements expected type code syntaxTree body
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih => exact @ErrorsFor.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih => exact @ErrorsFor.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih => exact @ErrorsFor.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH => exact @ErrorsFor.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH => exact @ErrorsFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH
  | @breaking context scope mode id node rest expected type found form => exact @ErrorsFor.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form
  | @continuing context scope mode id node rest expected type found form => exact @ErrorsFor.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH => exact @ErrorsFor.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopIH restIH
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih => exact @ErrorsFor.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining ih headErrors
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih => exact @ErrorsFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment rest expected type body found form head remaining ih headErrors
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH => exact @ErrorsFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH => exact @ErrorsFor.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopIH postErrors
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih => exact @ErrorsFor.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining ih
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih => exact @ErrorsFor.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining ih
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih => exact @ErrorsFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope expression expressionNode rest lowered body condition post statements expected type found child remaining ih
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih => exact @ErrorsFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining ih headErrors
  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih => exact @ErrorsFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment rest body condition post statements expected type head remaining ih headErrors
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts
      found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary
      children remaining patternContext childErrors remainingErrors childrenIH remainingIH =>
    exact @ErrorsFor.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childrenIH remainingIH

  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerIH =>
    exact .terminalBlock (unique := unique) (found := found) (form := form) (stops := stops) (issued := issued) innerIH
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    exact .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenIH elseIH

theorem Ready.errors {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (ready : Ready registry faults tree) : Errors registry faults tree := by
  exact ReadyFor.errors ready

end Tree

private theorem breaking_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · exact ScalarStatementViews.breaking unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.breaking_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible

private theorem continuing_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · exact ScalarStatementViews.continuing unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.continuing_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible

variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

abbrev PreservesAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev PreservesAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeader (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeader (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

private theorem sequence_stopped_preserves (unique : NodeOccurrencesUnique source) {context : SourceSemantics.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadPreserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped trace
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) executed with
      ⟨_, _, _, headTrace, tailTrace⟩ | ⟨headTrace, terminal⟩
    · cases stops headTrace
    · obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped (.control headTrace)
      cases represented with
      | fallthrough _ => cases terminal
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
          .returned payload, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .breaking next, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .continuing next, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) failed with
      ⟨rfl, headTrace⟩ | ⟨_, _, _, headTrace, tailTrace⟩
    · obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped (.fault headTrace)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · cases stops headTrace

private theorem sequence_stopped_reflects (_unique : NodeOccurrencesUnique source) {context : SourceSemantics.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadReflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  obtain ⟨wholeSize, original⟩ := evaluation_has_size evaluated
  rw [LoopRenaming.sequence] at evaluated original
  obtain ⟨headSize, middleStore, headValue, headSmaller, headSized⟩ := original.bind_computation
  have headEval := headSized.sound
  obtain ⟨outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    first valid environments heaps locals agrees actualTyped reference read unmapped headEval
  cases represented with
  | fallthrough next =>
    cases headTrace with | control headTrace => cases stops headTrace
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_returned _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.returned _),
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_failure _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.fault _),
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.breaking _),
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.continuing _),
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

include definitions registered extension meaning faithful observations catalogValid in
theorem Tree.preservesAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.ReadyFor diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      body.preserves functions definitions registered program evidence meaning contextValid unique environments heaps locals agrees actualTyped reference read unmapped trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨location, middle, allocated, tailTrace⟩ := source_view_absent unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tailTrace
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    rw [sequence_rename]
    rcases source_view_initialized unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
          environments heaps locals agrees actualTyped (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 tailTrace
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    rcases TypedScopedStatements.discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        meaning _ contextValid child expressionFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ contextValid child expressionFound
          environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tail
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (conditional_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (meaning := meaning context) (unique := unique) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_stopped_preserves unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_stopped_preserves unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (conditional_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (meaning := meaning context) (unique := unique) found form conditionFound conditionType conditionTree thenIH elseIH) (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @breaking context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (while_preserves functions program evidence (meaning context contextValid) found form conditionFound conditionTree nativeTyped unique loopIH) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact assignment_preserves_reachable functions extension program evidence (meaning context) faithful observations
      found form head (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors) unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact CompatibleBitNotStatements.assignment_preserves functions program evidence observations
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (header_preserves_reachable functions definitions registered extension program evidence meaning faithful observations unique found form (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, GenericForHeader.Tree.ErrorsFor.reachable errors⟩)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_preserves_reachable functions extension program evidence unique meaning definitions registered faithful observations
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH
    exact ⟨.nil completed, GenericForHeader.Tree.ErrorsFor.nil (policy := diagnosticPolicy) (next := completed)⟩
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same header, .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.initialized mono extended ordinary found sourceType child allocation annotation same header, .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := child) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.discard found child header, .discard (found := found) (value := child) errors⟩
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.assign head header, .assign (head := head) errors headErrors⟩

  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.bitNot head header, .bitNot (head := head) errors headErrors⟩

  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts
      found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary
      children remaining patternContext childErrors remainingErrors childrenIH remainingIH =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
      (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (head_preserves onError allocator functions definitions registered extension receipt ordinary
        patternContext catalogValid scrutineeFound casesTyped defaultTyped unique (meaning context) childrenIH)
      remainingIH

include definitions registered extension meaning faithful observations catalogValid in
theorem Tree.preservesAt (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.Ready registry faults tree) :
    PreservesAt (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply Tree.preservesAt_for (functions := functions) (tree := tree) (diagnosticPolicy := .unconditional)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations catalogValid in
theorem Tree.reflectsAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.ReadyFor diagnosticPolicy registry faults tree) :
    ReflectsAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      body.reflects functions definitions registered program evidence reflection contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    have continuation := (ContinuationAgreement.letE allocationEval).unwrap evaluated
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 continuation
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      reflection _ contextValid initial initialFound
        environments heaps locals agrees actualTyped initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed),
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 tailEval
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection _ contextValid child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨context, _, after, finalMap, finalWorld, TypedScopedStatements.head_fault mode rest (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        reflection _ contextValid child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
            ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨resultContext, outcome, after, finalMap, finalWorld,
            TypedScopedStatements.prepend (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (block_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (conditional_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (reflection := reflection context) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_stopped_reflects unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (block_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form innerIH) (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_stopped_reflects unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (conditional_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (reflection := reflection context) found form conditionFound conditionType conditionTree thenIH elseIH) (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @breaking context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    have nativeEval : Evaluates actual store ((LocalLoop.breaking type).rename ξ) (LocalLoop.breakingValue type) store := by
      simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.breakStmt (lookupStatement?_sound found) form) (.breaking environment),
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    have nativeEval : Evaluates actual store ((LocalLoop.continuing type).rename ξ) (LocalLoop.continuingValue type) store := by
      simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.continueStmt (lookupStatement?_sound found) form) (.continuing environment),
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (while_reflects functions program evidence (reflection context contextValid) found form conditionFound conditionTree nativeTyped loopIH
        (fun executed => loopTree.control_not_fault unique executed)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact assignment_reflects_reachable functions extension program evidence (meaning context) (reflection context) faithful observations functionTypes
      found form head (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors) unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact CompatibleBitNotStatements.assignment_reflects functions program evidence observations
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (header_reflects_reachable functions definitions registered extension program evidence meaning reflection faithful observations functionTypes unique found form (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, GenericForHeader.Tree.ErrorsFor.reachable errors⟩)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_reflects_reachable functions extension program evidence unique meaning reflection definitions registered faithful observations functionTypes
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH (fun executed => loopTree.control_not_fault unique executed)
    exact ⟨.nil completed, GenericForHeader.Tree.ErrorsFor.nil (policy := diagnosticPolicy) (next := completed)⟩
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same header, .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.initialized mono extended ordinary found sourceType child allocation annotation same header, .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := child) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.discard found child header, .discard (found := found) (value := child) errors⟩
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.assign head header, .assign (head := head) errors headErrors⟩

  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.bitNot head header, .bitNot (head := head) errors headErrors⟩

  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts
      found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary
      children remaining patternContext childErrors remainingErrors childrenIH remainingIH =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
      (globals := globals)  found (by intro expression; simp [form])
      (head_reflects onError allocator functions definitions registered extension receipt ordinary
        patternContext catalogValid scrutineeFound casesTyped defaultTyped  (reflection context) childrenIH)
      remainingIH

include definitions registered extension meaning reflection faithful observations catalogValid in
theorem Tree.reflectsAt (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.Ready registry faults tree) :
    ReflectsAt (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply Tree.reflectsAt_for (functions := functions) (tree := tree) (diagnosticPolicy := .unconditional)
  all_goals assumption

include definitions registered extension meaning faithful observations catalogValid in
theorem Tree.preserves_reachable {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.ReachableReady registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact tree.preservesAt_for (diagnosticPolicy := .reachable) functions definitions registered catalogValid extension program evidence meaning faithful observations unique errors
    contextValid environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension meaning faithful observations catalogValid in
theorem Tree.preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.Ready registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.preserves_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations catalogValid in
theorem Tree.reflects_reachable (functionTypes : FunctionRuntimeViews functions) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.ReachableReady registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact tree.reflectsAt_for (diagnosticPolicy := .reachable) functions definitions registered catalogValid extension program evidence meaning reflection faithful observations functionTypes unique errors
    contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

include definitions registered extension meaning reflection faithful observations catalogValid in
theorem Tree.reflects (functionTypes : FunctionRuntimeViews functions) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.Ready registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
