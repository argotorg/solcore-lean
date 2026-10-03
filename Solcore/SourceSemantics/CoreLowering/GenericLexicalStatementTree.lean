import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuations

/-! A single lexical statement algebra parameterized by static expression
certificates. Context changes are kept at each binding; scoped control restores
the lexical environment while retaining source and administrative allocations.
No execution or semantic induction hypothesis is stored in the tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericLexicalStatements
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev absentRequest := TypedLexicalControl.absentRequest
abbrev initializedRequest := TypedLexicalControl.initializedRequest
abbrev sequence := TypedLexicalControl.sequence

/-- The source which issued a stopped suffix remains separate from a local
metadata view. Statement lookups and binding provenance are unchanged. -/
structure StatementSourceIdentity (origin source : TypedSource) : Prop where
  owner : origin.owner = source.owner
  inputs : origin.inputs = source.inputs
  roots : origin.roots = source.roots
  lookup : ∀ id, origin.lookupStatement? id = source.lookupStatement? id

theorem StatementSourceIdentity.refl (source : TypedSource) : StatementSourceIdentity source source :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem StatementSourceIdentity.trans {origin middle source : TypedSource}
    (first : StatementSourceIdentity origin middle) (second : StatementSourceIdentity middle source) :
    StatementSourceIdentity origin source :=
  ⟨first.owner.trans second.owner, first.inputs.trans second.inputs, first.roots.trans second.roots,
    fun id => (first.lookup id).trans (second.lookup id)⟩

/-- Static stopping retains the original source and its independent control
summary. Prefix typing stays at its original source context. -/
def Stopped (source : TypedSource) (statements : List StatementId) : Prop :=
  ∃ origin summary, StatementSourceIdentity origin source ∧
    ReachableStatementContinuations.StoppingStatements origin statements summary

theorem Stopped.of_source {source : TypedSource} {statements : List StatementId} {summary : ControlSummary}
    (stops : ReachableStatementContinuations.StoppingStatements source statements summary) : Stopped source statements :=
  ⟨source, summary, .refl source, stops⟩

theorem Stopped.transport {origin source : TypedSource} {statements : List StatementId}
    (identity : StatementSourceIdentity origin source) (stops : Stopped origin statements) : Stopped source statements := by
  obtain ⟨issuing, summary, original, stopped⟩ := stops
  exact ⟨issuing, summary, original.trans identity, stopped⟩

/-- The dead code is the actual compiler suffix at its original issuing source.
A view transports provenance only; it does not assert callback reacceptance. -/
def IssuedSuffix (source : TypedSource) (scope : Scope) (mode : Bool) (statements : List StatementId)
    (type : Ty) (code : Expr) : Prop :=
  ∃ origin policy fuel reasonAt escaped, StatementSourceIdentity origin source ∧
    ReachableStatementContinuations.Issued policy fuel origin scope statements type reasonAt mode escaped code

theorem IssuedSuffix.of_accepted {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {mode : Bool} {statements : List StatementId} {type : Ty} {code : Expr}
    {reasonAt : ExpressionId → Word} {escaped : Word}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode escaped = .ok code) :
    IssuedSuffix source scope mode statements type code :=
  ⟨source, policy, fuel, reasonAt, escaped, .refl source, ⟨accepted⟩⟩

theorem IssuedSuffix.transport {origin source : TypedSource} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {type : Ty} {code : Expr}
    (identity : StatementSourceIdentity origin source) (issued : IssuedSuffix origin scope mode statements type code) :
    IssuedSuffix source scope mode statements type code := by
  obtain ⟨issuing, policy, fuel, reasonAt, escaped, original, accepted⟩ := issued
  exact ⟨issuing, policy, fuel, reasonAt, escaped, original.trans identity, accepted⟩

inductive Syntax (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
    SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop where
  | nil {context mode expected} (allowed : mode = false ∨ expected = .unit) : Syntax source expressionSyntax context mode [] expected
  | returnUnit {context mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) : Syntax source expressionSyntax context mode (id :: rest) .unit
  | returnValue {context mode id node expression expressionNode expected} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : expressionSyntax expression) : Syntax source expressionSyntax context mode (id :: rest) expected
  | tail {context id node expression expressionNode expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : expressionSyntax expression) : Syntax source expressionSyntax context true [id] expected
  | uninitialized {context nextContext mode id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source expressionSyntax nextContext mode rest expected) :
      Syntax source expressionSyntax context mode (id :: rest) expected

  | initialized {context nextContext mode id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : expressionSyntax initializer)
      (remaining : Syntax source expressionSyntax nextContext mode rest expected) :
      Syntax source expressionSyntax context mode (id :: rest) expected
  | discard {context mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : expressionSyntax expression)
      (remaining : Syntax source expressionSyntax context mode rest expected) : Syntax source expressionSyntax context mode (id :: rest) expected
  | block {context mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = .unit)
      (inner : Syntax source expressionSyntax context false statements expected)
      (remaining : Syntax source expressionSyntax context mode rest expected) : Syntax source expressionSyntax context mode (id :: rest) expected
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : expressionSyntax condition)
      (thenSyntax : Syntax source expressionSyntax context false thenBody expected)
      (elseSyntax : Syntax source expressionSyntax context false (elseBody.getD []) expected)
      (remaining : Syntax source expressionSyntax context mode rest expected) : Syntax source expressionSyntax context mode (id :: rest) expected

  | terminalBlock {context mode id node statements rest expected}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = expected)
      (inner : Syntax source expressionSyntax context false statements expected)
      (stops : Stopped source statements) : Syntax source expressionSyntax context mode (id :: rest) expected
  | terminalIf {context mode id node condition conditionNode thenBody elseBody rest expected}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
      (sourceType : node.type = expected)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : expressionSyntax condition)
      (thenSyntax : Syntax source expressionSyntax context false thenBody expected)
      (elseSyntax : Syntax source expressionSyntax context false elseBody expected)
      (thenStops : Stopped source thenBody) (elseStops : Stopped source elseBody) :
      Syntax source expressionSyntax context mode (id :: rest) expected


inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate) :
    SourceSemantics.Context → Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil {context scope mode expected type} (allowed : mode = false ∨ expected = .unit) :
      Tree layouts owner active frame globals onError values source expressions context scope mode [] expected type (LocalLoop.fallthrough type)
  | returnUnit {context scope mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit)
  | returnValue {context scope mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : expressions context scope expression lowered) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {context scope id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : expressions context scope expression lowered) :
      Tree layouts owner active frame globals onError values source expressions context scope true [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
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
      (remaining : Tree layouts owner active frame globals onError values source expressions
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions
        context scope mode (id :: rest) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : expressions context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressions nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions
        context scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : expressions context scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError values source expressions context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError values source expressions context scope false statements expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError values source expressions context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError values source expressions context scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError values source expressions context scope false statements expected type innerCode)
      (stops : Stopped source statements)
      (issued : IssuedSuffix source scope mode rest type suffix) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode suffix)
  | terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError values source expressions context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError values source expressions context scope false elseBody expected type elseCode)
      (thenStops : Stopped source thenBody) (elseStops : Stopped source elseBody)
      (issued : IssuedSuffix source scope mode rest type suffix) :
      Tree layouts owner active frame globals onError values source expressions context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix)


/-- The existing reached-context relation is shared by all profiles. -/
abbrev Reached := CompatibleStatementMixed.Reached

end Solcore.SourceSemantics.CoreLowering.GenericLexicalStatements
