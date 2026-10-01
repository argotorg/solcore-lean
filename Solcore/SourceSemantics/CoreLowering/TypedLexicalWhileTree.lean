import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlMeaning
import Solcore.SourceSemantics.CoreLowering.LoopExecution

/-! Ordinary while loops with lexical bindings and explicit loop transfers.
Native typing receipts concern the installed recursive closure only; source
meaning is supplied independently by the concrete expression and statement trees. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev absentRequest (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

abbrev initializedRequest := CompatibleStatementInitialized.request
abbrev sequence := CompatibleStatementInitialized.sequence

inductive Syntax (source : TypedSource) :
    SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop where
  | body {context mode statements expected} (syntaxTree : TypedLexicalControl.Syntax source context mode statements expected) :
      Syntax source context mode statements expected
  | uninitialized {context nextContext mode id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source nextContext mode rest expected) :
      Syntax source context mode (id :: rest) expected

  | initialized {context nextContext mode id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionTyped.Syntax source initializer)
      (remaining : Syntax source nextContext mode rest expected) :
      Syntax source context mode (id :: rest) expected
  | discard {context mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected
  | block {context mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = .unit)
      (inner : Syntax source context false statements expected)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : CompatibleExpressionTyped.Syntax source condition)
      (thenSyntax : Syntax source context false thenBody expected)
      (elseSyntax : Syntax source context false (elseBody.getD []) expected)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected

  | breaking {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Syntax source context mode (id :: rest) expected
  | continuing {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Syntax source context mode (id :: rest) expected
  | whileLoop {context mode id node condition conditionNode statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : CompatibleExpressionTyped.Syntax source condition)
      (loopBody : Syntax source context false statements expected)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (definitions : DataEnvironment) (administrative : Core.Context) :
    SourceSemantics.Context → Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | body {context scope mode statements expected type code}
      (syntaxTree : TypedLexicalControl.Syntax source context mode statements expected)
      (body : TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope mode statements expected type code
  | uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope mode (id :: rest) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source
        solved reasonAt definitions administrative nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope false statements expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope mode (id :: rest) expected type (LocalLoop.breaking type)
  | continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope mode (id :: rest) expected type (LocalLoop.continuing type)
  | whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope false statements expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body)

/-- Reuse the existing result-dependent lexical stopping relation. -/
abbrev Reached := CompatibleStatementMixed.Reached

/-- Fallthrough has no result payload; its enclosing return annotation is kept
on the native envelope even when that annotation is nominal or Boolean. -/
inductive FlowRep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
    (mapping : GeneralHeap.LocationMap) (world : StoreTyping) (faults : FunctionCalls.FaultRep)
    (expected : TypeSystem.Ty) (type : Ty) : Dynamic.ControlOutcome → Value → Prop where
  | fallthrough (environment : Dynamic.Environment) :
      FlowRep functions mapping world faults expected type (.fallthrough environment) (LocalLoop.fallthroughValue type)
  | returned {sourceValue coreValue}
      (payload : CompatiblePayload.ValueRep values.checked registry functions mapping world expected sourceValue coreValue type) :
      FlowRep functions mapping world faults expected type (.returned sourceValue) (LocalLoop.returnedValue coreValue)
  | fault {reason token} (matched : faults reason token) :
      FlowRep functions mapping world faults expected type (.fault reason) (.inLeft (LocalLoop.controlType type) (.word token))

  | breaking (environment : Dynamic.Environment) :
      FlowRep functions mapping world faults expected type (.breaking environment) (LocalLoop.breakingValue type)
  | continuing (environment : Dynamic.Environment) :
      FlowRep functions mapping world faults expected type (.continuing environment) (LocalLoop.continuingValue type)

theorem FlowRep.of_lexical {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel values.checked.catalog ambient}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome} {value : Value}
    (represented : TypedScopedStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value) :
    FlowRep (registry := registry) functions mapping world faults expected type outcome value := by
  cases represented with
  | fallthrough environment => exact .fallthrough environment
  | returned payload => exact .returned payload
  | fault matched => exact .fault matched

end Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile
