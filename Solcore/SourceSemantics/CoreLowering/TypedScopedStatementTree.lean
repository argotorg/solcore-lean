import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualTyped
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementMeaning
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
import Solcore.SourceSemantics.CoreLowering.LoopRenaming

/-! Typed compatible flow sequences select the actual source list judgment.
Function mode returns its final expression; scoped mode discards it. Empty
scoped branches may fall through at any enclosing result type. Both modes
use the existing ordinary Core loop envelope and typed expression certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedScopedStatements
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) (context : SourceSemantics.Context) :
    Bool → List StatementId → TypeSystem.Ty → Prop where
  | nil {mode expected} (allowed : mode = false ∨ expected = .unit) : Syntax source context mode [] expected
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) : Syntax source context mode (id :: rest) .unit
  | returnValue {mode id node expression expressionNode expected} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression) : Syntax source context mode (id :: rest) expected
  | tail {id node expression expressionNode expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression) : Syntax source context true [id] expected
  | discard {mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected

inductive Tree (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil {mode expected type} (allowed : mode = false ∨ expected = .unit) :
      Tree readFuel values source context solved reasonAt scope mode [] expected type (LocalLoop.fallthrough type)
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Tree readFuel values source context solved reasonAt scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit)
  | returnValue {mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope mode (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope true [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | discard {mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree readFuel values source context solved reasonAt scope mode rest expected type body) :
      Tree readFuel values source context solved reasonAt scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)

/-- The exact independent source judgment selected by production lowering. -/
def Executes (mode : Bool) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId)
    (finalContext : SourceSemantics.Context) (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  if mode then Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before
    statements finalContext outcome after
  else Dynamic.StatementsExecuteOutcome program context evidence source environment before
    statements finalContext outcome after

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

end Solcore.SourceSemantics.CoreLowering.TypedScopedStatements
