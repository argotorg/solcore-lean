import Solcore.SourceSemantics.Staging.CallBoundary

/-!
# The recursive staged profile

A finite profile in which every callee, argument and selected body uses the same staged traces. The
source-to-Core theorems are stated over it. Main declarations: `Staging.Recursive.Scope`,
`Staging.Recursive.Registry`, `Staging.Recursive.Expression`, `Staging.Recursive.Statements`,
`Staging.Recursive.Applies`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveScope
/-! Independent invocation scopes for recursively staged traces. The scope
keeps the original caller marker/stage table and both declaration and local
substitutions. Selecting a closure's scope is a static provenance obligation.
It is not inferred from source/Core function typing. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference

structure Origin where
  declaration : Resolved.DeclarationId
  declarationSubstitution : TypeSystem.ParameterSubstitution
  localSubstitution : TypeSystem.Substitution

structure Scope where
  origin : Origin
  source : TypedSource
  owned : source.owner = origin.declaration
  context : Context
  evidence : Dynamic.EvidenceEnvironment
  guards : CallBoundary.Frame

/-- A profile supplies this relation from retained code/source receipts. It
may distinguish equal erased function types by their complete local context.
The fields constrain every selected body scope to the actual source closure. -/
structure Registry where
  Closure : Dynamic.Closure → Scope → Prop
  source : ∀ {function scope}, Closure function scope → scope.source = function.source
  context : ∀ {function scope}, Closure function scope → scope.context = function.context
  evidence : ∀ {function scope}, Closure function scope → scope.evidence = function.evidence

/-- Nested failures retain the original failing scope and occurrence. The
caller cannot relabel them with its own return marker or active substitution. -/
inductive Failure where
  | semantic (reason : Dynamic.SemanticFault)
  | stage (scope : Scope) (call : ExpressionId) (reason : CallGuard.Fault)

inductive Outcome where
  | value (value : Dynamic.Value)
  | fault (failure : Failure)

inductive ValuesOutcome where
  | values (values : List Dynamic.Value)
  | fault (failure : Failure)

inductive BodyOutcome where
  | fallthrough (environment : Dynamic.Environment)
  | breaking (environment : Dynamic.Environment)
  | continuing (environment : Dynamic.Environment)
  | returned (value : Dynamic.Value)
  | fault (failure : Failure)

/-- Exact uncoerced occurrence with its original requirements, independently of
any compiler. Existing ordinary occurrences default to no requirements. -/
def Occurrence (scope : Scope) (id : ExpressionId) (form : ExpressionForm)
    (requirements : List RequirementId := []) : Prop :=
  ∃ node, ContainsExpression scope.source id node ∧ node.form = form ∧
    node.requirements = requirements ∧ node.coercions = []

/-- Forms whose raw evaluation has no expression or callable-body child.
Their independent atomic Dynamic rules can be reused without bypassing a
nested stage guard. Output coercions are separately excluded. -/
inductive AtomicForm : ExpressionForm → Prop where
  | unit : AtomicForm (.tuple [])
  | literal (value) : AtomicForm (.literal value)
  | integerLiteral (source resolution) : AtomicForm (.integerLiteral source resolution)
  | reference (name resolution) : AtomicForm (.reference name resolution)
  | lambda (parameters result body) : AtomicForm (.lambda parameters result body)
  | proxy (inner) : AtomicForm (.proxy inner)

end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveBareTarget
/-! Bare targets retain their cell before the right-hand expression runs.
This receipt has no expression evaluator: an empty projection path only looks
up the lexical reference and reads its current optional value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

inductive BareTarget (environment : Environment) (heap : Heap)
    (place : PlaceResolution) : ResolvedPlace → Prop where
  | intro {location cell initial}
      (bare : place.projections = [])
      (lookup : Environment.LooksUp environment place.root location)
      (read : Heap.Reads heap location cell)
      (value : RootInitialValue cell initial) :
      BareTarget environment heap place
        { location := location, rootType := cell.type, valueType := place.type,
          projections := [], selected := initial }

namespace BareTarget

theorem resolves {environment : Environment} {heap : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (snapshot : BareTarget environment heap place target)
    (program : Program) (context : Context) (evidence : EvidenceEnvironment)
    (source : TypedSource) :
    SourcePlaceResolves program context evidence source environment heap place target heap := by
  cases snapshot with
  | intro bare lookup read value =>
      exact .intro lookup read (bare ▸ .nil) read value .nil

theorem of_resolves {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (bare : place.projections = [])
    (resolved : SourcePlaceResolves program context evidence source environment before place target after) :
    before = after ∧ BareTarget environment before place target := by
  cases resolved with
  | intro lookup initialRead evaluate currentRead initial selection =>
      rw [bare] at evaluate
      cases evaluate
      cases selection
      exact ⟨rfl, .intro bare lookup currentRead initial⟩

end BareTarget
end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveBareBitNot
/-! Bare unary updates have no projection or right-hand expression. A failed
leaf therefore retains exactly its incoming heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

theorem bitNot_fault_heap {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap} {place : PlaceResolution}
    {reason : SemanticFault} (bare : place.projections = [])
    (failed : SourcePlaceBitNotFaults program context evidence source environment
      before place reason after) : after = before := by
  cases failed with
  | target failed =>
    cases failed with
    | unbound | dangling => rfl
    | projectionExpression _ _ failed => rw [bare] at failed; cases failed
    | danglingAfterProjections _ _ evaluated _
    | projectionRead _ _ evaluated _ _ _
    | uninitialized _ _ evaluated _ _ _ _ =>
      rw [bare] at evaluated
      cases evaluated
      rfl
  | uninitialized resolved _ | operand resolved _ _ =>
    exact (BareTarget.of_resolves bare resolved).1.symm

end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveControlTransferFacts
/-! Control transfers at a staged function boundary. Loop bodies retain their
transfers until the enclosing loop consumes them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.BodyOutcome

def NoEscapedControl (outcome : BodyOutcome) : Prop :=
  (∀ environment, outcome ≠ .breaking environment) ∧
  (∀ environment, outcome ≠ .continuing environment)

theorem NoEscapedControl.returned (value : Dynamic.Value) :
    NoEscapedControl (.returned value) := by
  constructor <;> intro other equal <;> cases equal

theorem NoEscapedControl.fault (failure : Failure) :
    NoEscapedControl (.fault failure) := by
  constructor <;> intro other equal <;> cases equal

theorem NoEscapedControl.fallthrough (environment : Dynamic.Environment) :
    NoEscapedControl (.fallthrough environment) := by
  constructor <;> intro other equal <;> cases equal

end Solcore.SourceSemantics.Staging.Recursive.BodyOutcome
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveProjectedTarget
/-! Ordered projection keys and pure snapshots for staged projected writes.
Key expressions run before the getter. The final write retains the snapshot
while reconstructing the path from the root reached after the RHS. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- Members have no expression child; every index occurrence stays in order. -/
def keys : List PlaceProjection → List ExpressionId
  | [] => []
  | .member _ _ :: rest => keys rest
  | .index key :: rest => key :: keys rest

inductive Values : List PlaceProjection → List Dynamic.Value → List EvaluatedProjection → Prop where
  | nil : Values [] [] []
  | member {name index rest values evaluated} (tail : Values rest values evaluated) :
      Values (.member name index :: rest) values (.member name index :: evaluated)
  | index {key rest value values evaluated} (tail : Values rest values evaluated) :
      Values (.index key :: rest) (value :: values) (.index value :: evaluated)

/-- Root lookup and the first read precede all key effects. -/
inductive RootReady (environment : Environment) (heap : Heap) (place : PlaceResolution) : Prop where
  | intro {location cell}
      (lookup : Environment.LooksUp environment place.root location)
      (read : Heap.Reads heap location cell) : RootReady environment heap place

inductive RootFault (environment : Environment) (heap : Heap) (place : PlaceResolution) : SemanticFault → Prop where
  | unbound (missing : environment.Unbound place.root) : RootFault environment heap place (.unboundLocal place.root)
  | dangling {location} (lookup : Environment.LooksUp environment place.root location)
      (missing : heap.Dangling location) : RootFault environment heap place (.danglingLocation location)

/-- The second root read and pure getter use the actual heap after all keys. -/
inductive Snapshot (environment : Environment) (before after : Heap) (place : PlaceResolution)
    (values : List Dynamic.Value) : ResolvedPlace → Prop where
  | intro {location initialCell currentCell evaluated initial selected}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (currentRead : Heap.Reads after location currentCell)
      (initialValue : RootInitialValue currentCell initial)
      (selection : ProjectionsRead initial evaluated selected) :
      Snapshot environment before after place values
        { location := location, rootType := currentCell.type, valueType := place.type,
          projections := evaluated, selected := selected }

/-- Getter failures occur only after the complete successful key row. -/
inductive GetterFault (environment : Environment) (before after : Heap) (place : PlaceResolution)
    (values : List Dynamic.Value) : SemanticFault → Prop where
  | dangling {location initialCell evaluated}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (missing : after.Dangling location) : GetterFault environment before after place values (.danglingLocation location)
  | projection {location initialCell currentCell evaluated initial reason}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (currentRead : Heap.Reads after location currentCell)
      (initialValue : RootInitialValue currentCell initial)
      (fault : ProjectionsFaults initial evaluated reason) : GetterFault environment before after place values reason
  | uninitialized {location initialCell currentCell evaluated}
      (lookup : Environment.LooksUp environment place.root location)
      (initialRead : Heap.Reads before location initialCell)
      (ordered : Values place.projections values evaluated)
      (currentRead : Heap.Reads after location currentCell)
      (empty : currentCell.value = none)
      (notMapping : ¬ ∃ keyType valueType, currentCell.type = .mapping keyType valueType)
      (nonempty : evaluated ≠ []) : GetterFault environment before after place values (.uninitializedLocation location)

/-- The latest root path is checked before the saved-snapshot leaf modifier. -/
inductive WriteFault (operator : Syntax.ValueAssignOp) (target : ResolvedPlace)
    (right : Dynamic.Value) (heap : Heap) : SemanticFault → Prop where
  | operands {currentCell initial currentSelected}
      (currentRead : Heap.Reads heap target.location currentCell)
      (rootType : currentCell.type = target.rootType)
      (initialValue : RootInitialValue currentCell initial)
      (pathRead : ProjectionsRead initial target.projections currentSelected)
      (invalid : AssignmentOperandsInvalid operator target.selected right) :
      WriteFault operator target right heap (.invalidAssignmentOperands operator)
  | panic {currentCell initial currentSelected code}
      (currentRead : Heap.Reads heap target.location currentCell)
      (rootType : currentCell.type = target.rootType)
      (initialValue : RootInitialValue currentCell initial)
      (pathRead : ProjectionsRead initial target.projections currentSelected)
      (panics : AssignmentOperandsPanic operator target.selected right code) :
      WriteFault operator target right heap (.panic code)
  | structural {currentCell initial reason}
      (currentRead : Heap.Reads heap target.location currentCell)
      (rootType : currentCell.type = target.rootType)
      (initialValue : RootInitialValue currentCell initial)
      (fault : ProjectionsFaults initial target.projections reason) :
      WriteFault operator target right heap reason

theorem Values.evaluates {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {projections : List PlaceProjection}
    {values : List Dynamic.Value} {evaluated : List EvaluatedProjection}
    (ordered : Values projections values evaluated)
    (trace : ExpressionsEvaluate program context evidence source environment before (keys projections) values after) :
    SourceProjectionsEvaluate program context evidence source environment before projections evaluated after := by
  induction ordered generalizing before with
  | nil => cases trace; exact .nil
  | member _ ih => exact .member (ih trace)
  | index _ ih =>
      cases trace with
      | cons head tail => exact .index head (ih tail)

theorem keys_fault {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {projections : List PlaceProjection} {reason : SemanticFault}
    (trace : ExpressionsFault program context evidence source environment before (keys projections) reason after) :
    SourceProjectionsFault program context evidence source environment before projections reason after := by
  induction projections generalizing before with
  | nil => cases trace
  | cons projection rest ih =>
      cases projection with
      | member name index => exact .memberTail (ih trace)
      | index key =>
          cases trace with
          | head failed => exact .indexHead failed
          | tail head tail => exact .indexTail head (ih tail)

theorem Snapshot.resolves {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {place : PlaceResolution} {values : List Dynamic.Value} {target : ResolvedPlace}
    (snapshot : Snapshot environment before after place values target)
    (trace : ExpressionsEvaluate program context evidence source environment before (keys place.projections) values after) :
    SourcePlaceResolves program context evidence source environment before place target after := by
  cases snapshot with
  | intro lookup initialRead ordered currentRead initialValue selection =>
      exact .intro lookup initialRead (ordered.evaluates trace) currentRead initialValue selection

theorem RootFault.source {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {heap : Heap} {place : PlaceResolution} {reason : SemanticFault}
    (failed : RootFault environment heap place reason) :
    SourcePlaceFaults program context evidence source environment heap place reason heap := by
  cases failed with
  | unbound missing => exact .unbound missing
  | dangling lookup missing => exact .dangling lookup missing

theorem RootReady.key_fault {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {place : PlaceResolution} {reason : SemanticFault}
    (ready : RootReady environment before place)
    (failed : ExpressionsFault program context evidence source environment before (keys place.projections) reason after) :
    SourcePlaceFaults program context evidence source environment before place reason after := by
  cases ready with
  | intro lookup read => exact .projectionExpression lookup read (keys_fault failed)

theorem GetterFault.source {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before after : Heap} {place : PlaceResolution} {values : List Dynamic.Value} {reason : SemanticFault}
    (failed : GetterFault environment before after place values reason)
    (trace : ExpressionsEvaluate program context evidence source environment before (keys place.projections) values after) :
    SourcePlaceFaults program context evidence source environment before place reason after := by
  cases failed with
  | dangling lookup read ordered missing =>
      exact .danglingAfterProjections lookup read (ordered.evaluates trace) missing
  | projection lookup initialRead ordered currentRead initialValue fault =>
      exact .projectionRead lookup initialRead (ordered.evaluates trace) currentRead initialValue fault
  | uninitialized lookup initialRead ordered currentRead empty notMapping nonempty =>
      exact .uninitialized lookup initialRead (ordered.evaluates trace) currentRead empty notMapping nonempty

theorem WriteFault.source {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource} {environment : Environment}
    {before targetHeap rhsHeap : Heap} {place : PlaceResolution} {target : ResolvedPlace}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {right : Dynamic.Value} {reason : SemanticFault}
    (failed : WriteFault operator target right rhsHeap reason)
    (resolved : SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (evaluated : ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap) :
    SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap := by
  cases failed with
  | operands read root initial path invalid => exact .operands resolved evaluated read root initial path invalid
  | panic read root initial path panics => exact .panic resolved evaluated read root initial path panics
  | structural read root initial fault => exact .structuralUpdate resolved evaluated read root initial fault

end Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveTrace
/-! A finite recursive staged profile. Every callee, argument and selected body
uses these same mutually recursive judgments. Staging rejection propagates
unchanged through lexical scopes and call returns, retaining exact prefix heaps.

The profile covers atomic forms, groups, ordered tuples, nominal constructor
payloads, mapping indices, primitive and evidence-selected operators,
conditionals, direct declarations, indirect calls and builtins. Output coercion
paths on atomic forms and direct calls retain their original source metadata.
Bodies cover ordinary and generalized lets, bare plain assignments, discards, scoped blocks,
conditional statements, finite while and for loops, ordered match arms, returns,
and scoped break and continue transfers.
Blocks and conditional arms restore lexical bindings while keeping heap effects.
Projected value assignments retain ordered keys, their getter snapshot, and the actual final write.
Generalized reads retain the actual dictionary instantiation and recursively staged output coercions. These judgments do not assert coverage of the full current compiler. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- Leaving a match arm restores lexical bindings, while its heap is retained. -/
def BodyOutcome.restore (environment : Environment) : BodyOutcome → BodyOutcome
  | .fallthrough _ => .fallthrough environment
  | .breaking _ => .breaking environment
  | .continuing _ => .continuing environment
  | .returned value => .returned value
  | .fault failure => .fault failure

/-- For-header completion retains its actual live bindings; headers do not transfer control. -/
inductive ForItemsOutcome where
  | done (environment : Dynamic.Environment)
  | fault (failure : Failure)

inductive BodyResult : TypeSystem.Ty → BodyOutcome → Outcome → Prop where
  | returned {type value} : BodyResult type (.returned value) (.value value)
  | breaking {type environment} :
      BodyResult type (.breaking environment) (.fault (.semantic .controlEscapedFunction))
  | continuing {type environment} :
      BodyResult type (.continuing environment) (.fault (.semantic .controlEscapedFunction))
  | unit {environment} : BodyResult .unit (.fallthrough environment) (.value .unit)
  | fault {type failure} : BodyResult type (.fault failure) (.fault failure)

/-- A named body has an empty lexical capture and its independent full
invocation dictionary. This view is not itself a global callable identity;
global application also requires genuine program instantiation and Covers. -/
def globalView (body : BodyInstance) (evidence : EvidenceEnvironment) (roots : List StatementId) : Closure where
  parameters := body.source.inputs
  resultType := body.resultType
  body := roots
  source := body.source
  captured := []
  context := body.context
  evidence := evidence

/-- A method body uses a neutral scope view with its selected dictionary.
This record is neither an ordinary global identity nor a source lambda value. -/
def methodView (body : BodyInstance) (evidence : EvidenceEnvironment) (roots : List StatementId) : Closure :=
  globalView body evidence roots

/-- Mapping lookup decides only after both children have finished. This
independent Source relation keeps the original key and value types. -/
inductive IndexOutcome (base key : Dynamic.Value) : Outcome → Prop where
  | found {keyType valueType entries value}
      (shape : base = .mapping keyType valueType entries)
      (located : MappingLookup key entries value) : IndexOutcome base key (.value value)
  | default {keyType valueType entries value}
      (shape : base = .mapping keyType valueType entries)
      (absent : MappingAbsent key entries) (defaulted : DefaultValue valueType value) :
      IndexOutcome base key (.value value)
  | shape (invalid : ¬ MappingValue base) :
      IndexOutcome base key (.fault (.semantic .invalidProjection))
  | keyType {keyType valueType entries actual}
      (shape : base = .mapping keyType valueType entries)
      (typed : ValueRuntimeType key actual) (mismatch : runtimeType actual ≠ runtimeType keyType) :
      IndexOutcome base key (.fault (.semantic (.typeMismatch keyType (runtimeType actual))))
  | unavailable {keyType valueType entries}
      (shape : base = .mapping keyType valueType entries)
      (typed : ValueRuntimeTypeMatches key keyType) (absent : MappingAbsent key entries)
      (missing : ¬ Defaultable valueType) :
      IndexOutcome base key (.fault (.semantic (.missingMappingDefault valueType)))

mutual
  inductive Expression (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionId → Outcome → Heap → Prop where
    | atomicValue {scope context environment before after id node value}
        (contains : ContainsExpression scope.source id node)
        (atomic : AtomicForm node.form) (uncoerced : node.coercions = [])
        (valueRule : ExpressionFormEvaluates program context scope.evidence scope.source environment before
          node.form node.requirements [] value after) :
        Expression program registry scope context environment before id (.value value) after
    | atomicFault {scope context environment before after id node reason}
        (contains : ContainsExpression scope.source id node)
        (atomic : AtomicForm node.form) (uncoerced : node.coercions = [])
        (faultRule : ExpressionFormFaults program context scope.evidence scope.source environment before
          node.form node.requirements [] reason after) :
        Expression program registry scope context environment before id (.fault (.semantic reason)) after
    | generalizedLocal {scope context environment before after id node name binder owned
          location cell function substitution produced outcome}
        (contains : ContainsExpression scope.source id node)
        (form : node.form = .reference name (.local binder))
        (layout : OrdinaryRequirementLayout node.requirements node.coercions owned)
        (lookup : Environment.LooksUp environment binder location)
        (read : Heap.Reads before location cell)
        (descriptor : cell.generalized = some function)
        (contextFields : RuntimeContextFields function.definitionContext context)
        (instantiation : LocalSchemeRuntimeInstantiation context scope.evidence
          function.binder node.rawType owned substitution produced)
        (coercions : CoercionPath program registry scope context before node.coercions
          (.closure (function.instantiate substitution
            (produced ++ scope.evidence.applySubstitution substitution))) outcome after) :
        Expression program registry scope context environment before id outcome after
    | generalizedLocalRequirement {scope context environment heap id node name binder owned
          location cell function substitution failed}
        (contains : ContainsExpression scope.source id node)
        (form : node.form = .reference name (.local binder))
        (layout : OrdinaryRequirementLayout node.requirements node.coercions owned)
        (lookup : Environment.LooksUp environment binder location)
        (read : Heap.Reads heap location cell)
        (descriptor : cell.generalized = some function)
        (contextFields : RuntimeContextFields function.definitionContext context)
        (selection : LocalSchemeRuntimeSelection context function.binder node.rawType owned substitution)
        (fault : RequirementsFault context scope.evidence owned
          (instantiateLocalSchemePredicates substitution function.binder) failed) :
        Expression program registry scope context environment heap id
          (.fault (.semantic (.unsatisfiedRequirement failed))) heap
    | group {scope context environment before after id inner outcome}
        (occurrence : Occurrence scope id (.group inner))
        (child : Expression program registry scope context environment before inner outcome after) :
        Expression program registry scope context environment before id outcome after
    | pair {scope context environment before middle after id left right a b}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (first : Expression program registry scope context environment before left (.value a) middle)
        (second : Expression program registry scope context environment middle right (.value b) after) :
        Expression program registry scope context environment before id (.value (.product a b)) after
    | pairLeftFault {scope context environment before after id left right failure}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (child : Expression program registry scope context environment before left (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | pairRightFault {scope context environment before middle after id left right value failure}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (first : Expression program registry scope context environment before left (.value value) middle)
        (second : Expression program registry scope context environment middle right (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | tupleValue {scope context environment before after id elements values packed}
        (occurrence : Occurrence scope id (.tuple elements))
        (children : Expressions program registry scope context environment before elements (.values values) after)
        (pack : ValuesPack values packed) :
        Expression program registry scope context environment before id (.value packed) after
    | tupleFault {scope context environment before after id elements failure}
        (occurrence : Occurrence scope id (.tuple elements))
        (children : Expressions program registry scope context environment before elements (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | constructorValue {scope context environment before after id instantiation arguments values}
        (occurrence : Occurrence scope id (.constructor instantiation arguments))
        (valid : DataConstructorInstantiation.Valid context instantiation)
        (children : Expressions program registry scope context environment before arguments (.values values) after) :
        Expression program registry scope context environment before id (.value (.constructed instantiation values)) after
    | constructorFault {scope context environment before after id instantiation arguments failure}
        (occurrence : Occurrence scope id (.constructor instantiation arguments))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | indexBaseFault {scope context environment before after id base key failure}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry scope context environment before base (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | indexKeyFault {scope context environment before middle after id base key value failure}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry scope context environment before base (.value value) middle)
        (second : Expression program registry scope context environment middle key (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | indexResult {scope context environment before middle after id base key baseValue keyValue outcome}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry scope context environment before base (.value baseValue) middle)
        (second : Expression program registry scope context environment middle key (.value keyValue) after)
        (result : IndexOutcome baseValue keyValue outcome) :
        Expression program registry scope context environment before id outcome after
    | unary {scope context environment before after id operator operand input output}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry scope context environment before operand (.value input) after)
        (applies : UnaryPrimitiveApplies operator input output) :
        Expression program registry scope context environment before id (.value output) after
    | unaryOperandFault {scope context environment before after id operator operand failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.unary operator operand) requirements)
        (child : Expression program registry scope context environment before operand (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | unaryInvalid {scope context environment before after id operator operand input}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry scope context environment before operand (.value input) after)
        (invalid : UnaryPrimitiveOperandInvalid operator input) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.invalidUnaryOperand operator))) after
    | binaryLeftFault {scope context environment before after id left operator right failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
        (first : Expression program registry scope context environment before left (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | binaryLeftInvalid {scope context environment before after id left operator right input}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value input) after)
        (invalid : BinaryLeftOperandInvalid operator input) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.invalidBinaryOperands operator))) after
    | binaryShortCircuit {scope context environment before after id left operator right input output}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value input) after)
        (circuit : ShortCircuits operator input output) :
        Expression program registry scope context environment before id (.value output) after
    | binaryRightFault {scope context environment before middle after id left operator right input failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
        (first : Expression program registry scope context environment before left (.value input) middle)
        (continues : EvaluatesRightOperand operator input)
        (second : Expression program registry scope context environment middle right (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | binary {scope context environment before middle after id left operator right a b output}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry scope context environment middle right (.value b) after)
        (applies : BinaryPrimitiveApplies operator a b output) :
        Expression program registry scope context environment before id (.value output) after
    | binaryInvalid {scope context environment before middle after id left operator right a b}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry scope context environment middle right (.value b) after)
        (invalid : BinaryPrimitiveOperandsInvalid operator a b) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.invalidBinaryOperands operator))) after
    | binaryPanic {scope context environment before middle after id left operator right a b code}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry scope context environment middle right (.value b) after)
        (panics : BinaryPrimitivePanics operator a b code) :
        Expression program registry scope context environment before id (.fault (.semantic (.panic code))) after
    | unaryMethod {scope context environment before argumentsHeap bound after id operator operand input
          requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (occurrence : Occurrence scope id (.unary operator operand) requirements)
        (dispatch : UnaryTraitDispatch operator traitName methodName)
        (method : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
        (operandTrace : Expression program registry scope context environment before operand (.value input) argumentsHeap)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [input] bodyEnvironment bound)
        (body : StatementsIn program registry true child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Expression program registry scope context environment before id result after
    | binaryMethod {scope context environment before middle argumentsHeap bound after id left operator right a b
          requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
        (dispatch : BinaryTraitDispatch operator traitName methodName)
        (method : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
        (first : Expression program registry scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry scope context environment middle right (.value b) argumentsHeap)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [a, b] bodyEnvironment bound)
        (body : StatementsIn program registry true child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Expression program registry scope context environment before id result after
    | conditional {scope context environment before middle after id condition yes no truth outcome}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : Expression program registry scope context environment middle (if truth then yes else no) outcome after) :
        Expression program registry scope context environment before id outcome after
    | conditionalFault {scope context environment before after id condition yes no failure}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | builtinArgumentsFault {scope context environment before after id callee arguments function failure}
        (occurrence : Occurrence scope id (.call callee arguments (.builtinFunction function)))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | builtinApplied {scope context environment before argumentsHeap after id callee arguments function values outcome}
        (occurrence : Occurrence scope id (.call callee arguments (.builtinFunction function)))
        (children : Expressions program registry scope context environment before arguments (.values values) argumentsHeap)
        (invocation : Applies program registry scope context argumentsHeap (.builtin ⟨function⟩) values outcome after) :
        Expression program registry scope context environment before id outcome after
    | directArgumentsFault {scope context environment before after id callee arguments instantiation name failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.call callee arguments (.declaration instantiation)) requirements)
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | directApplied {scope context environment before argumentsHeap after id callee arguments instantiation name values evidence outcome}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.call callee arguments (.declaration instantiation)) requirements)
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
        (children : Expressions program registry scope context environment before arguments (.values values) argumentsHeap)
        (callEvidence : DirectCallProducesEvidence context scope.evidence requirements [] instantiation.predicates evidence)
        (invocation : Applies program registry scope context argumentsHeap (.global ⟨instantiation, evidence⟩) values outcome after) :
        Expression program registry scope context environment before id outcome after
    | calleeFault {scope context environment before after id callee arguments metadata failure}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | notCallable {scope context environment before after id callee arguments metadata value}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) after)
        (invalid : ¬ CallableValue value) :
        Expression program registry scope context environment before id (.fault (.semantic .notCallable)) after
    | rejected {scope context environment before after id callee arguments metadata value reason}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) after)
        (guard : CallBoundary.GuardRejects scope.guards id arguments value reason) :
        Expression program registry scope context environment before id (.fault (.stage scope id reason)) after
    | argumentsFault {scope context environment before middle after id callee arguments metadata value failure}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) middle)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry scope context environment middle arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | sourceArity {scope context environment before middle after id callee arguments metadata value values}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) middle)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry scope context environment middle arguments (.values values) after)
        (mismatch : arguments.length ≠ metadata.argumentCount) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.argumentArityMismatch metadata.argumentCount arguments.length))) after
    | applied {scope context environment before calleeHeap argumentsHeap after id callee arguments metadata value values outcome}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (uncoerced : metadata.argumentCoercions = [])
        (child : Expression program registry scope context environment before callee (.value value) calleeHeap)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry scope context environment calleeHeap arguments (.values values) argumentsHeap)
        (arity : arguments.length = metadata.argumentCount)
        (invocation : Applies program registry scope context argumentsHeap value values outcome after) :
        Expression program registry scope context environment before id outcome after

    | coercedValue {scope context environment before middle after id node value outcome}
        (contains : ContainsExpression scope.source id node)
        (nonempty : node.coercions ≠ [])
        (raw : RawForm program registry scope context environment before node.form
          node.requirements node.coercions (.value value) middle)
        (path : CoercionPath program registry scope context middle node.coercions value outcome after) :
        Expression program registry scope context environment before id outcome after
    | coercedFault {scope context environment before after id node failure}
        (contains : ContainsExpression scope.source id node)
        (nonempty : node.coercions ≠ [])
        (raw : RawForm program registry scope context environment before node.form
          node.requirements node.coercions (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after

  inductive Expressions (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → List ExpressionId → ValuesOutcome → Heap → Prop where
    | nil {scope context environment heap} :
        Expressions program registry scope context environment heap [] (.values []) heap
    | cons {scope context environment before middle after id ids value values}
        (head : Expression program registry scope context environment before id (.value value) middle)
        (tail : Expressions program registry scope context environment middle ids (.values values) after) :
        Expressions program registry scope context environment before (id :: ids) (.values (value :: values)) after
    | headFault {scope context environment before after id ids failure}
        (head : Expression program registry scope context environment before id (.fault failure) after) :
        Expressions program registry scope context environment before (id :: ids) (.fault failure) after
    | tailFault {scope context environment before middle after id ids value failure}
        (head : Expression program registry scope context environment before id (.value value) middle)
        (tail : Expressions program registry scope context environment middle ids (.fault failure) after) :
        Expressions program registry scope context environment before (id :: ids) (.fault failure) after

  inductive Applies (program : Program) (registry : Registry) :
      Scope → Context → Heap → Value → List Value → Outcome → Heap → Prop where
    | builtin {scope context heap function arguments value}
        (primitive : BuiltinApplies function.id arguments value) :
        Applies program registry scope context heap (.builtin function) arguments (.value value) heap
    | builtinArity {scope context heap function arguments}
        (mismatch : function.id.parameterTypes.length ≠ arguments.length) :
        Applies program registry scope context heap (.builtin function) arguments
          (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length arguments.length))) heap
    | builtinType {scope context heap function arguments expected actual}
        (arity : function.id.parameterTypes.length = arguments.length)
        (mismatch : ValuesFirstTypeMismatch arguments function.id.parameterTypes expected actual) :
        Applies program registry scope context heap (.builtin function) arguments
          (.fault (.semantic (.typeMismatch expected actual))) heap
    | closureArity {scope context heap function arguments}
        (mismatch : function.parameters.length ≠ arguments.length) :
        Applies program registry scope context heap (.closure function) arguments
          (.fault (.semantic (.argumentArityMismatch function.parameters.length arguments.length))) heap
    | globalArity {scope context heap function arguments bodyInstance}
        (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
        (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
        Applies program registry scope context heap (.global function) arguments
          (.fault (.semantic (.argumentArityMismatch bodyInstance.source.inputs.length arguments.length))) heap
    | global {scope context before bound after function arguments environment
          parameterTypes bodyContext finalContext bodyInstance roots child outcome result}
        (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
        (covers : function.evidence.Covers bodyInstance.context)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (globalView bodyInstance function.evidence roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
        (body : StatementsIn program registry true child bodyContext environment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Applies program registry scope context before (.global function) arguments result after
    | closure {scope context before copied bound after function arguments entry environment parameterTypes bodyContext finalContext child outcome result}
        (selected : registry.Closure function child)
        (valid : ClosureFrame program function)
        (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes bodyContext)
        (copy : EnvironmentCopies function.source function.captured before entry copied)
        (allocate : BindersAllocate entry copied function.parameters arguments environment bound)
        (body : StatementsIn program registry true child bodyContext environment bound function.body finalContext outcome after)
        (resultRule : BodyResult function.resultType outcome result) :
        Applies program registry scope context before (.closure function) arguments result after

  inductive StatementsIn (program : Program) (registry : Registry) :
      Bool → Scope → Context → Environment → Heap → List StatementId → Context → BodyOutcome → Heap → Prop where
    | nil {mode scope context environment heap} :
        StatementsIn program registry mode scope context environment heap [] context (.fallthrough environment) heap
    | returnUnit {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt none) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context (.returned .unit) heap
    | continuing {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .continueStmt) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context (.continuing environment) heap
    | breaking {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .breakStmt) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context (.breaking environment) heap
    | returnValue {mode scope context environment before after id rest node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry scope context environment before expression (.value value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | returnFault {mode scope context environment before after id rest node expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | tail {scope context environment before after id node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry scope context environment before expression (.value value) after) :
        StatementsIn program registry true scope context environment before [id] context (.returned value) after
    | discard {mode scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression true)
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | expressionFault {mode scope context environment before after id rest node expression semicolon failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression semicolon)
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    /-- A non-tail branch expression discards its value even at the end of its arm. -/
    | discardValue {scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (next : StatementsIn program registry false scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry false scope context environment before (id :: rest) finalContext outcome after
    | ifConditionFault {mode scope context environment before after id rest node condition thenBody elseBody failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | ifReturned {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | ifContinuing {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.continuing innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.continuing environment) after
    | ifBreaking {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.breaking innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.breaking environment) after
    | ifFault {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    /-- Branch-local bindings leave scope; all writes and allocations remain in its reached heap. -/
    | ifFallthrough {mode scope context innerContext finalContext environment innerEnvironment before middle branchHeap after
          id rest node condition thenBody elseBody truth outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.fallthrough innerEnvironment) branchHeap)
        (next : StatementsIn program registry mode scope context environment branchHeap rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | blockReturned {mode scope context innerContext environment before after id rest node statements value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | blockContinuing {mode scope context innerContext environment before after id rest node statements innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.continuing innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.continuing environment) after
    | blockBreaking {mode scope context innerContext environment before after id rest node statements innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.breaking innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.breaking environment) after
    | blockFault {mode scope context innerContext environment before after id rest node statements failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    /-- A block restores its entry bindings while retaining every write and allocation. -/
    | blockFallthrough {mode scope context innerContext finalContext environment innerEnvironment before middle after id rest node statements outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.fallthrough innerEnvironment) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | matchReturned {mode scope context environment before after id rest node resolution value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | matchContinuing {mode scope context environment before after id rest node resolution}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.continuing environment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.continuing environment) after
    | matchBreaking {mode scope context environment before after id rest node resolution}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.breaking environment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.breaking environment) after
    | matchFault {mode scope context environment before after id rest node resolution failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | matchFallthrough {mode scope context finalContext environment before middle after id rest node resolution outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.fallthrough environment) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | forInitializerFault {mode scope context failedContext environment before after id rest node initializer condition post body failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer failedContext (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | forReturned {mode scope context loopContext environment loopEnvironment before middle after id rest node initializer condition post body value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry scope loopContext loopEnvironment middle condition post body (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | forFault {mode scope context loopContext environment loopEnvironment before middle after id rest node initializer condition post body failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry scope loopContext loopEnvironment middle condition post body (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | forFallthrough {mode scope context loopContext finalContext environment loopEnvironment before middle loopHeap after
          id rest node initializer condition post body outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry scope loopContext loopEnvironment middle condition post body (.fallthrough loopEnvironment) loopHeap)
        (next : StatementsIn program registry mode scope context environment loopHeap rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | whileReturned {mode scope context environment before after id rest node condition statements value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry scope context environment before condition statements (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | whileFault {mode scope context environment before after id rest node condition statements failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry scope context environment before condition statements (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | whileFallthrough {mode scope context finalContext environment before middle after id rest node condition statements outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry scope context environment before condition statements (.fallthrough environment) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    /-- The target snapshot precedes the RHS; the write uses its actual final heap. -/
    | bitNotProjected {mode scope context finalContext environment before targetHeap written after assignment values target updated id rest node outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (write : ResolvedPlaceWrites
          (fun _ replacement => BitNotSnapshot target.selected replacement)
          targetHeap target updated written)
        (next : StatementsIn program registry mode scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | bitNotProjectedRootFault {mode scope context environment before assignment id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault (.semantic reason)) before
    | bitNotProjectedKeysFault {mode scope context environment before after assignment id rest node failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | bitNotProjectedGetterFault {mode scope context environment before after assignment values id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault (.semantic reason)) after
    | assignProjected {mode scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated id rest node outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry scope context environment targetHeap rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : StatementsIn program registry mode scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | assignProjectedRootFault {mode scope context environment before assignment operator rhs id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault (.semantic reason)) before
    | assignProjectedKeysFault {mode scope context environment before after assignment operator rhs id rest node failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | assignProjectedGetterFault {mode scope context environment before after assignment operator rhs values id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault (.semantic reason)) after
    | assignProjectedRhsFault {mode scope context environment before targetHeap after assignment operator rhs values target id rest node failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry scope context environment targetHeap rhs (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | assignProjectedWriteFault {mode scope context environment before targetHeap after assignment operator rhs values target right id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry scope context environment targetHeap rhs (.value right) after)
        (failed : ProjectedTarget.WriteFault operator target right after reason) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault (.semantic reason)) after
    | assignBare {mode scope context finalContext environment before middle written after
          id rest node assignment operator rhs value target updated outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : StatementsIn program registry mode scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | assignBareFault {mode scope context environment before after id rest node assignment operator rhs target failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | assignBareOperands {mode scope context environment before after id rest node assignment operator rhs
          target right currentCell initial currentSelected}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        StatementsIn program registry mode scope context environment before (id :: rest) context
          (.fault (.semantic (.invalidAssignmentOperands operator))) after
    | assignBarePanic {mode scope context environment before after id rest node assignment operator rhs
          target right currentCell initial currentSelected code}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (panics : AssignmentOperandsPanic operator target.selected right code) :
        StatementsIn program registry mode scope context environment before (id :: rest) context
          (.fault (.semantic (.panic code))) after
    | assignBareUnbound {mode scope context environment heap id rest node assignment operator rhs}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (bare : assignment.target.projections = [])
        (missing : environment.Unbound assignment.target.root) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context
          (.fault (.semantic (.unboundLocal assignment.target.root))) heap
    | assignBareDangling {mode scope context environment heap id rest node assignment operator rhs location}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (bare : assignment.target.projections = [])
        (lookup : Environment.LooksUp environment assignment.target.root location)
        (missing : heap.Dangling location) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context
          (.fault (.semantic (.danglingLocation location))) heap
    /-- Bare unary assignment reads its snapshot and performs a real write,
    without an expression child for the compiler's administrative Unit. -/
    | bitNotBare {mode scope context finalContext environment before written after
          id rest node assignment target updated outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (snapshot : BareTarget environment before assignment.target target)
        (write : ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
          before target updated written)
        (next : StatementsIn program registry mode scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | bitNotBareFault {mode scope context environment before id rest node assignment reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (bare : assignment.target.projections = [])
        (failed : SourcePlaceBitNotFaults program context scope.evidence scope.source environment
          before assignment.target reason before) :
        StatementsIn program registry mode scope context environment before (id :: rest) context
          (.fault (.semantic reason)) before
    | letUninitialized {mode scope context middleContext finalContext environment before bound after id rest node binder location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : StatementsIn program registry mode scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | letInitialized {mode scope context middleContext finalContext environment before middle bound after id rest node binder expression value location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : StatementsIn program registry mode scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | letGeneralized {mode scope context middleContext finalContext environment before snapshotHeap bound after
          id rest node binder initializer captured function location outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .letDecl binder (some initializer))
        (snapshot : EnvironmentCopies scope.source environment before captured snapshotHeap)
        (captures : GeneralizedClosureCaptures context scope.source captured binder initializer function)
        (polymorphic : binder.scheme.quantified ≠ [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.AllocatesGeneralized snapshotHeap function location bound)
        (next : StatementsIn program registry mode scope middleContext
          ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | letFault {mode scope context environment before after id rest node binder expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after


  /-- Finite loop iterations restore their original lexical scope while retaining
  all condition and body heap effects. Break leaves the loop; continue tests again. -/
  inductive While (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionId → List StatementId → BodyOutcome → Heap → Prop where
    | done {scope context environment before after condition statements}
        (test : Expression program registry scope context environment before condition (.value (.bool false)) after) :
        While program registry scope context environment before condition statements (.fallthrough environment) after
    | conditionFault {scope context environment before after condition statements failure}
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        While program registry scope context environment before condition statements (.fault failure) after
    | returned {scope context innerContext environment before middle after condition statements value}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.returned value) after) :
        While program registry scope context environment before condition statements (.returned value) after
    | breakFromBody {scope context innerContext environment before middle after condition statements innerEnvironment}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.breaking innerEnvironment) after) :
        While program registry scope context environment before condition statements (.fallthrough environment) after
    | bodyFault {scope context innerContext environment before middle after condition statements failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.fault failure) after) :
        While program registry scope context environment before condition statements (.fault failure) after
    | next {scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.fallthrough innerEnvironment) bodyHeap)
        (next : While program registry scope context environment bodyHeap condition statements outcome after) :
        While program registry scope context environment before condition statements outcome after
    | continueNext {scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.continuing innerEnvironment) bodyHeap)
        (next : While program registry scope context environment bodyHeap condition statements outcome after) :
        While program registry scope context environment before condition statements outcome after


  /-- The original source's ordered pattern decision and real allocations are
  independent of the compiler. Selected bodies keep the same staged registry. -/
  inductive Match (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → MatchResolution → BodyOutcome → Heap → Prop where
    | scrutineeFault {scope context environment before after resolution failure}
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.fault failure) after) :
        Match program registry scope context environment before resolution (.fault failure) after
    | patternFault {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (allocated : Heap.Allocates middle node.type (some value) location hidden)
        (invalid : MatchCasesPatternFault context value resolution.cases) :
        Match program registry scope context environment before resolution (.fault (.semantic .invalidPattern)) hidden
    | arm {scope context armContext finalContext environment armEnvironment before middle hidden bound after
          resolution node value location statements bindings outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
        (extended : BindersExtend scope.source.owner context (bindings.map Prod.fst) armContext)
        (allocated : BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
        (body : StatementsIn program registry false scope armContext armEnvironment bound statements finalContext outcome after) :
        Match program registry scope context environment before resolution (outcome.restore environment) after
    | default {scope context finalContext environment before middle hidden after resolution node value location statements outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
        (body : StatementsIn program registry false scope context environment hidden statements finalContext outcome after) :
        Match program registry scope context environment before resolution (outcome.restore environment) after
    | noBranch {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
        Match program registry scope context environment before resolution (.fallthrough environment) hidden


  /-- Ordered ordinary for-header effects retain their actual lexical context.
  A fault carries the context reached before the failing item. -/
  inductive ForItems (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → List ForItemForm → Context → ForItemsOutcome → Heap → Prop where
    | empty {scope context environment heap} :
        ForItems program registry scope context environment heap [] context (.done environment) heap
    | absent {scope context middleContext finalContext environment before bound after binder rest location outcome}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : ForItems program registry scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        ForItems program registry scope context environment before (.letDecl binder none :: rest) finalContext outcome after
    | initialized {scope context middleContext finalContext environment before middle bound after binder initializer rest value location outcome}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (child : Expression program registry scope context environment before initializer (.value value) middle)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : ForItems program registry scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        ForItems program registry scope context environment before (.letDecl binder (some initializer) :: rest) finalContext outcome after
    | initializedGeneralized {scope context middleContext finalContext environment before snapshotHeap bound
          after binder initializer rest captured function location outcome}
        (snapshot : EnvironmentCopies scope.source environment before captured snapshotHeap)
        (captures : GeneralizedClosureCaptures context scope.source captured binder initializer function)
        (polymorphic : binder.scheme.quantified ≠ [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.AllocatesGeneralized snapshotHeap function location bound)
        (next : ForItems program registry scope middleContext
          ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        ForItems program registry scope context environment before
          (.letDecl binder (some initializer) :: rest) finalContext outcome after
    | initializerFault {scope context environment before after binder initializer rest failure}
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry scope context environment before initializer (.fault failure) after) :
        ForItems program registry scope context environment before (.letDecl binder (some initializer) :: rest) context (.fault failure) after
    | expression {scope context finalContext environment before middle after expression rest value outcome}
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (next : ForItems program registry scope context environment middle rest finalContext outcome after) :
        ForItems program registry scope context environment before (.expression expression :: rest) finalContext outcome after
    | expressionFailure {scope context environment before after expression rest failure}
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        ForItems program registry scope context environment before (.expression expression :: rest) context (.fault failure) after
    | projectedBitNot {scope context finalContext environment before targetHeap written after assignment values target updated rest outcome}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (write : ResolvedPlaceWrites
          (fun _ replacement => BitNotSnapshot target.selected replacement)
          targetHeap target updated written)
        (next : ForItems program registry scope context environment written rest finalContext outcome after) :
        ForItems program registry scope context environment before (.assignBitNot assignment :: rest) finalContext outcome after
    | projectedBitNotRootFault {scope context environment before assignment rest reason}
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        ForItems program registry scope context environment before (.assignBitNot assignment :: rest) context (.fault (.semantic reason)) before
    | projectedBitNotKeysFault {scope context environment before after assignment rest failure}
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        ForItems program registry scope context environment before (.assignBitNot assignment :: rest) context (.fault failure) after
    | projectedBitNotGetterFault {scope context environment before after assignment values rest reason}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        ForItems program registry scope context environment before (.assignBitNot assignment :: rest) context (.fault (.semantic reason)) after
    | projectedAssignment {scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated rest outcome}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry scope context environment targetHeap rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : ForItems program registry scope context environment written rest finalContext outcome after) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) finalContext outcome after
    | projectedAssignmentRootFault {scope context environment before assignment operator rhs rest reason}
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) before
    | projectedAssignmentKeysFault {scope context environment before after assignment operator rhs rest failure}
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault failure) after
    | projectedAssignmentGetterFault {scope context environment before after assignment operator rhs values rest reason}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) after
    | projectedAssignmentRhsFault {scope context environment before targetHeap after assignment operator rhs values target rest failure}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry scope context environment targetHeap rhs (.fault failure) after) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault failure) after
    | projectedAssignmentWriteFault {scope context environment before targetHeap after assignment operator rhs values target right rest reason}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry scope context environment targetHeap rhs (.value right) after)
        (failed : ProjectedTarget.WriteFault operator target right after reason) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) after
    | assignment {scope context finalContext environment before middle written after assignment operator rhs value target updated rest outcome}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : ForItems program registry scope context environment written rest finalContext outcome after) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) finalContext outcome after
    | assignmentFailure {scope context environment before after assignment operator rhs target rest failure}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.fault failure) after) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault failure) after
    | assignmentOperands {scope context environment before after assignment operator rhs target right
          currentCell initial currentSelected rest}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.invalidAssignmentOperands operator))) after
    | assignmentPanic {scope context environment before after assignment operator rhs target right
          currentCell initial currentSelected rest code}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (panics : AssignmentOperandsPanic operator target.selected right code) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.panic code))) after
    | unbound {scope context environment heap assignment operator rhs rest}
        (bare : assignment.target.projections = [])
        (missing : environment.Unbound assignment.target.root) :
        ForItems program registry scope context environment heap (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.unboundLocal assignment.target.root))) heap
    | dangling {scope context environment heap assignment operator rhs rest location}
        (bare : assignment.target.projections = [])
        (lookup : Environment.LooksUp environment assignment.target.root location)
        (missing : heap.Dangling location) :
        ForItems program registry scope context environment heap (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.danglingLocation location))) heap
    | bitNot {scope context finalContext environment before written after assignment target updated rest outcome}
        (snapshot : BareTarget environment before assignment.target target)
        (write : ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
          before target updated written)
        (next : ForItems program registry scope context environment written rest finalContext outcome after) :
        ForItems program registry scope context environment before (.assignBitNot assignment :: rest) finalContext outcome after
    | bitNotFault {scope context environment before assignment rest reason}
        (bare : assignment.target.projections = [])
        (failed : SourcePlaceBitNotFaults program context scope.evidence scope.source environment
          before assignment.target reason before) :
        ForItems program registry scope context environment before (.assignBitNot assignment :: rest) context
          (.fault (.semantic reason)) before


  /-- Finite for iteration runs each post header in the original loop scope.
  Body/post local bindings are restored, while their heap effects persist. -/
  inductive ForLoop (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionId → List ForItemForm → List StatementId → BodyOutcome → Heap → Prop where
    | testFault {scope context environment before after condition post body failure}
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | finished {scope context environment before after condition post body}
        (test : Expression program registry scope context environment before condition (.value (.bool false)) after) :
        ForLoop program registry scope context environment before condition post body (.fallthrough environment) after
    | bodyFailure {scope context innerContext environment before middle after condition post body failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | returnedFromBody {scope context innerContext environment before middle after condition post body value}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.returned value) after) :
        ForLoop program registry scope context environment before condition post body (.returned value) after
    | forBreakFromBody {scope context innerContext environment before middle after condition post body innerEnvironment}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.breaking innerEnvironment) after) :
        ForLoop program registry scope context environment before condition post body (.fallthrough environment) after
    | postFailure {scope context innerContext postContext environment innerEnvironment before middle bodyHeap after condition post body failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.fallthrough innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | continuePostFailure {scope context innerContext postContext environment innerEnvironment before middle bodyHeap after condition post body failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.continuing innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | iterate {scope context innerContext postContext environment innerEnvironment postEnvironment before middle bodyHeap postHeap after condition post body outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.fallthrough innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.done postEnvironment) postHeap)
        (next : ForLoop program registry scope context environment postHeap condition post body outcome after) :
        ForLoop program registry scope context environment before condition post body outcome after

    | continueIterate {scope context innerContext postContext environment innerEnvironment postEnvironment before middle bodyHeap postHeap after condition post body outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.continuing innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.done postEnvironment) postHeap)
        (next : ForLoop program registry scope context environment postHeap condition post body outcome after) :
        ForLoop program registry scope context environment before condition post body outcome after

  /-- The original form before its retained output path. Child expressions keep
  the same source scope, full requirements and actual coercion partition. -/
  inductive RawForm (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionForm → List RequirementId →
      List SourceInference.CoercionStep → Outcome → Heap → Prop where
    | rawAtomicValue {scope context environment before after form requirements coercions value}
        (atomic : AtomicForm form)
        (valueRule : ExpressionFormEvaluates program context scope.evidence scope.source environment before
          form requirements coercions value after) :
        RawForm program registry scope context environment before form requirements coercions (.value value) after
    | rawAtomicFault {scope context environment before after form requirements coercions reason}
        (atomic : AtomicForm form)
        (faultRule : ExpressionFormFaults program context scope.evidence scope.source environment before
          form requirements coercions reason after) :
        RawForm program registry scope context environment before form requirements coercions (.fault (.semantic reason)) after
    | rawDirectArgumentsFault {scope context environment before after callee arguments instantiation name failure requirements coercions}
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        RawForm program registry scope context environment before (.call callee arguments (.declaration instantiation))
          requirements coercions (.fault failure) after
    | rawDirectApplied {scope context environment before argumentsHeap after callee arguments instantiation name values evidence outcome requirements coercions}
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
        (children : Expressions program registry scope context environment before arguments (.values values) argumentsHeap)
        (callEvidence : DirectCallProducesEvidence context scope.evidence requirements coercions instantiation.predicates evidence)
        (invocation : Applies program registry scope context argumentsHeap (.global ⟨instantiation, evidence⟩) values outcome after) :
        RawForm program registry scope context environment before (.call callee arguments (.declaration instantiation))
          requirements coercions outcome after

  /-- An actual conversion edge uses either the independent primitive rule or
  a selected method body in its authentic staged scope. -/
  inductive CoercionStep (program : Program) (registry : Registry) :
      Scope → Context → Heap → SourceInference.CoercionStep → Value → Outcome → Heap → Prop where
    | coercionPrimitive {scope context heap step input output}
        (noSourceMethod : ∀ bodyInstance dictionary,
          ¬ OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
            step.requirements bodyInstance dictionary)
        (applies : CoercionApplies context step input output) :
        CoercionStep program registry scope context heap step input (.value output) heap
    | coercionRequirement {scope context heap step input failed}
        (fault : RequirementListFaults context scope.evidence step.requirements failed) :
        CoercionStep program registry scope context heap step input (.fault (.semantic (.unsatisfiedRequirement failed))) heap
    | coercionPrimitiveInput {scope context heap step input actual}
        (noSourceMethod : ∀ bodyInstance dictionary,
          ¬ OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
            step.requirements bodyInstance dictionary)
        (invalid : PrimitiveCoercionInputInvalid step input)
        (actualType : ValueRuntimeType input actual) :
        CoercionStep program registry scope context heap step input (.fault (.semantic (.typeMismatch step.source actual))) heap
    | coercionMethod {scope context before bound after step input bodyInstance dictionary roots child
          parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (method : OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
          step.requirements bodyInstance dictionary)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs [input] bodyEnvironment bound)
        (body : StatementsIn program registry true child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        CoercionStep program registry scope context before step input result after

  /-- Ordered retained edges stop at the first semantic or staged failure. -/
  inductive CoercionPath (program : Program) (registry : Registry) :
      Scope → Context → Heap → List SourceInference.CoercionStep → Value → Outcome → Heap → Prop where
    | coercionsNil {scope context heap value} :
        CoercionPath program registry scope context heap [] value (.value value) heap
    | coercionsCons {scope context before middle after step steps input converted outcome}
        (head : CoercionStep program registry scope context before step input (.value converted) middle)
        (tail : CoercionPath program registry scope context middle steps converted outcome after) :
        CoercionPath program registry scope context before (step :: steps) input outcome after
    | coercionsFault {scope context before after step steps input failure}
        (head : CoercionStep program registry scope context before step input (.fault failure) after) :
        CoercionPath program registry scope context before (step :: steps) input (.fault failure) after

end

/-- Function bodies retain the original interface. Branch arms use `StatementsIn ... false`. -/
abbrev Statements (program : Program) (registry : Registry) := StatementsIn program registry true
namespace Statements
export StatementsIn (breaking continuing ifBreaking ifContinuing blockBreaking blockContinuing matchBreaking matchContinuing nil returnUnit returnValue returnFault tail discard expressionFault
  assignProjected assignProjectedRootFault assignProjectedKeysFault assignProjectedGetterFault assignProjectedRhsFault assignProjectedWriteFault
  bitNotProjected bitNotProjectedRootFault bitNotProjectedKeysFault bitNotProjectedGetterFault
  bitNotBare bitNotBareFault assignBare assignBareFault assignBareOperands assignBarePanic assignBareUnbound assignBareDangling letUninitialized letInitialized letGeneralized letFault
  ifConditionFault ifReturned ifFault ifFallthrough blockReturned blockFault blockFallthrough whileReturned whileFault whileFallthrough matchReturned matchFault matchFallthrough
  forInitializerFault forReturned forFault forFallthrough)
end Statements

end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveTraceProperties
/-! Origin and prefix properties of the recursive staged profile. Every
propagated stage failure is backed by an actual rejected guard at the retained
source occurrence, including failures escaping a selected closure body, an ordered tuple element,
or a primitive operand.
Short-circuited operands contribute no trace and therefore cannot introduce a failure. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

def Generated (scope : Scope) (call : ExpressionId) (reason : CallGuard.Fault) : Prop :=
  ∃ callee arguments metadata value,
    Occurrence scope call (.call callee arguments (.indirect metadata)) ∧
    CallBoundary.GuardRejects scope.guards call arguments value reason

private def ExpressionOrigin (outcome : Outcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private def ValuesOrigin (outcome : ValuesOutcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private def BodyOrigin (outcome : BodyOutcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private def ForItemsOrigin (outcome : ForItemsOutcome) : Prop :=
  ∀ (originScope : Scope) (call : ExpressionId) (reason : CallGuard.Fault),
    outcome = .fault (.stage originScope call reason) → Generated originScope call reason

private theorem body_result_stage {type : TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome}
    (converted : BodyResult type outcome result) {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : result = .fault (.stage originScope call reason)) : outcome = .fault (.stage originScope call reason) := by
  cases converted with
  | returned => cases failed
  | breaking => cases failed
  | continuing => cases failed
  | unit => cases failed
  | fault => exact congrArg BodyOutcome.fault (Outcome.fault.inj failed)

local macro "retain_stage_origin" : tactic =>
  `(tactic| (
    case rejected occurrence child guard ih =>
      intro s c r same
      cases same
      exact ⟨_, _, _, _, occurrence, guard⟩
    case tupleFault occurrence children ih | constructorFault occurrence children ih
      | builtinArgumentsFault occurrence children ih
      | directArgumentsFault occurrence calleeOccurrence children ih =>
      intro s c r same
      cases same
      exact ih s c r rfl
    case coercionMethod method roots selected parameters allocate body result bodyIH =>
      intro s c r same
      exact bodyIH s c r (body_result_stage result same)
    case unaryMethod occurrence dispatch method operand roots selected parameters allocate body result operandIH bodyIH =>
      intro s c r same
      exact bodyIH s c r (body_result_stage result same)
    case binaryMethod occurrence dispatch method first continues second roots selected parameters allocate body result firstIH secondIH bodyIH =>
      intro s c r same
      exact bodyIH s c r (body_result_stage result same)
    case global instantiates covers roots selected parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case closure selected valid parameters allocate body result ih =>
      intro s c r same
      exact ih s c r (body_result_stage result same)
    case arm contains scrutinee hidden selected extended allocated body scrutineeIH bodyIH =>
      rename_i outcome
      cases outcome <;> simp_all [BodyOutcome.restore, BodyOrigin]
    case default contains scrutinee hidden selected body scrutineeIH bodyIH =>
      rename_i outcome
      cases outcome <;> simp_all [BodyOutcome.restore, BodyOrigin]
    case indexResult occurrence first second result ih_first ih_second =>
      cases result <;> simp_all [ExpressionOrigin]
    all_goals simp_all [ExpressionOrigin, ValuesOrigin, BodyOrigin, ForItemsOrigin]
  ))

theorem Expression.stage_origin {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {id : ExpressionId} {outcome : Outcome}
    (trace : Expression program registry scope context environment before id outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using Expression.rec
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem Expressions.stage_origin {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {ids : List ExpressionId} {outcome : ValuesOutcome}
    (trace : Expressions program registry scope context environment before ids outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ValuesOrigin outcome := by
    clear failed
    induction trace using Expressions.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem Applies.stage_origin {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {value : Value} {values : List Value} {outcome : Outcome}
    (trace : Applies program registry scope context before value values outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using Applies.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem StatementsIn.stage_origin {mode : Bool} {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {statements : List StatementId} {outcome : BodyOutcome}
    (trace : StatementsIn program registry mode scope context environment before statements finalContext outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : BodyOrigin outcome := by
    clear failed
    induction trace using StatementsIn.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

namespace Statements
export StatementsIn (stage_origin)
end Statements

/-- Successful argument traversal retains source arity without a separate
assumption about a runtime argument evaluator. -/
theorem Expressions.length {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {values : List Value}
    (trace : Expressions program registry scope context environment before ids (.values values) after) :
    ids.length = values.length := by
  induction ids generalizing before values with
  | nil => cases trace; rfl
  | cons head rest ih =>
    cases trace with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

/-- The body scope is the selected closure scope. The caller's return marker,
source table and cumulative local substitution are not substituted for it. -/
theorem Applies.closure_scope {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {function : Closure} {values : List Value} {outcome : Outcome}
    (trace : Applies program registry scope context before (.closure function) values outcome after)
    (arity : function.parameters.length = values.length) :
    ∃ child, registry.Closure function child ∧ child.source = function.source ∧
      child.context = function.context ∧ child.evidence = function.evidence := by
  cases trace with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected _ _ _ _ _ =>
    exact ⟨_, selected, registry.source selected, registry.context selected, registry.evidence selected⟩

theorem RawForm.stage_origin {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep} {outcome : Outcome}
    (trace : RawForm program registry scope context environment before form requirements coercions outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using RawForm.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem CoercionStep.stage_origin {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionStep program registry scope context before step input outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using CoercionStep.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_11 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

theorem CoercionPath.stage_origin {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionPath program registry scope context before steps input outcome after)
    {originScope : Scope} {call : ExpressionId} {reason : CallGuard.Fault}
    (failed : outcome = .fault (.stage originScope call reason)) : Generated originScope call reason := by
  have origin : ExpressionOrigin outcome := by
    clear failed
    induction trace using CoercionPath.rec
      (motive_1 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_2 := fun _ _ _ _ _ outcome _ _ => ValuesOrigin outcome)
      (motive_3 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_4 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_5 := fun _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_6 := fun _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_7 := fun _ _ _ _ _ _ outcome _ _ => ForItemsOrigin outcome)
      (motive_8 := fun _ _ _ _ _ _ _ outcome _ _ => BodyOrigin outcome)
      (motive_9 := fun _ _ _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
      (motive_10 := fun _ _ _ _ _ outcome _ _ => ExpressionOrigin outcome)
    retain_stage_origin
  exact origin originScope call reason failed

end Solcore.SourceSemantics.Staging.Recursive
end
