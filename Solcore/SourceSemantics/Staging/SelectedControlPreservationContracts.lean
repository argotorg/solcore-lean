import Solcore.SourceSemantics.Staging.SelectedPreservationProjections
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

structure ControlPreserved (context : Context) (before after : Heap)
    (type : Ty) (outcome : BodyOutcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  returned : ∀ value, outcome = .returned value → ValueHasType context after value type

variable (program : Program) (registry : Registry)

def WhileAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context bodyFinal : Context} {environment : Dynamic.Environment}
    {before after : Heap} {condition : ExpressionId} {statements : List StatementId}
    {outcome : BodyOutcome} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context condition .bool →
    StatementsHaveType scope.source control.enterLoop context statements bodyFinal facts →
    Size.While program registry size scope context environment before condition statements outcome after →
    ControlPreserved context before after control.returnType outcome

def MatchAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {resolution : MatchResolution} {outcome : BodyOutcome}
    {control : ControlContext} {type : Ty} {caseFacts : List BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context resolution.scrutinee type →
    MatchCasesHaveType scope.source control context type resolution.cases caseFacts →
    (∀ statements, resolution.defaultBody = some statements →
      ∃ final facts, StatementsHaveType scope.source control context statements final facts) →
    Size.Match program registry size scope context environment before resolution outcome after →
    ControlPreserved context before after control.returnType outcome

def ForItemsAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context staticFinal runtimeFinal : Context} {environment : Dynamic.Environment}
    {before after : Heap} {items : List ForItemForm} {outcome : ForItemsOutcome} {control : ControlContext},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ForItemsHaveType scope.source control context items staticFinal →
    Size.ForItems program registry size scope context environment before items runtimeFinal outcome after →
    ItemsPreserved context staticFinal runtimeFinal before after outcome

def ForLoopAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context bodyFinal postFinal : Context} {environment : Dynamic.Environment}
    {before after : Heap} {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    {outcome : BodyOutcome} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context condition .bool →
    StatementsHaveType scope.source control.enterLoop context body bodyFinal facts →
    ForItemsHaveType scope.source control.enterLoop context post postFinal →
    Size.ForLoop program registry size scope context environment before condition post body outcome after →
    ControlPreserved context before after control.returnType outcome

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
