import Solcore.Test.SourceCoreChosenOrdinaryAcceptedTyping
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeader

/-! The original accepted fixture's outer let and indirect call receive a
finite declarative Source typing proof. All retained binder and node types
come from checks over the unchanged fixture; native typing is independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterTyping
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture CallableIndexedNamedGeneration

def functionType : TypeSystem.Ty := .function parameterType wordType

/-- These are actual retained fields missing from the earlier lookup receipt. -/
structure Metadata (fixture : AcceptedFixture) : Prop where
  owned : fixture.graph.binder.id.owner = (source fixture.packet.named).owner
  scheme : fixture.graph.binder.scheme = .mono functionType
  requirements : fixture.graph.binder.schemeRequirements = []
  ordinary : fixture.graph.binder.comptime = false
  initializedType : fixture.graph.initialized.type = .unit
  leftType : fixture.parentRows.left.type = wordType
  rightType : fixture.parentRows.right.type = wordType
  calleeType : fixture.graph.callee.type = functionType
  argumentType : fixture.graph.argument.type = parameterType
  returnedType : fixture.graph.outerReturn.type = wordType
  resultType : fixture.packet.named.specialized.function.inferredBodyType = wordType

/-- The finite checker returns the equations of the original fields. -/
def metadata (fixture : AcceptedFixture) : Except String (PLift (Metadata fixture)) :=
  if correct : fixture.graph.binder.id.owner = (source fixture.packet.named).owner ∧
      fixture.graph.binder.scheme = .mono functionType ∧ fixture.graph.binder.schemeRequirements = [] ∧
      fixture.graph.binder.comptime = false ∧ fixture.graph.initialized.type = .unit ∧
      fixture.parentRows.left.type = wordType ∧ fixture.parentRows.right.type = wordType ∧
      fixture.graph.callee.type = functionType ∧ fixture.graph.argument.type = parameterType ∧
      fixture.graph.outerReturn.type = wordType ∧
      fixture.packet.named.specialized.function.inferredBodyType = wordType then
    let ⟨owned, scheme, requirements, ordinary, initializedType, leftType, rightType,
      calleeType, argumentType, returnedType, resultType⟩ := correct
    .ok ⟨⟨owned, scheme, requirements, ordinary, initializedType, leftType, rightType,
      calleeType, argumentType, returnedType, resultType⟩⟩
  else .error "actual outer binder or occurrence types differ"

variable {fixture : AcceptedFixture}

def localContext (fixture : AcceptedFixture) : SourceSemantics.Context :=
  (runtimeContext fixture.packet).withLocal fixture.graph.binder.id
    fixture.graph.binder.scheme fixture.graph.binder.schemeRequirements

theorem local_binders : TypeParameterBindersWellFormed (localContext fixture) :=
  SourceCoreChosenOrdinaryAcceptedTyping.initial_binders

theorem function_admissible (context : SourceSemantics.Context)
    (binders : TypeParameterBindersWellFormed context) : TypeAdmissible context functionType :=
  .function (.product (.word binders) (.word binders)) (.word binders)

theorem Metadata.binder (given : Metadata fixture) :
    BinderWellFormed (runtimeContext fixture.packet) (source fixture.packet.named).owner fixture.graph.binder := by
  refine ⟨given.owned, ?_, ?_, fun _ => given.requirements⟩
  · rw [given.scheme]
    exact SchemeWellFormed.monoAdmissible (function_admissible _ SourceCoreChosenOrdinaryAcceptedTyping.initial_binders)
  · rw [given.scheme]
    intro metavariable member
    cases member

theorem fresh : LocalFresh (runtimeContext fixture.packet) fixture.graph.binder.id := by
  constructor <;> exact List.not_mem_nil

theorem Metadata.extended (given : Metadata fixture) :
    BinderExtends (source fixture.packet.named).owner (runtimeContext fixture.packet)
      fixture.graph.binder (localContext fixture) := .intro given.binder fresh

theorem Metadata.generalizes (given : Metadata fixture) :
    SchemeGeneralizes (runtimeContext fixture.packet) fixture.graph.binder.scheme := by
  rw [given.scheme]
  rfl

def letFacts : StatementFacts := {
  type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }

/-- The already proved lambda initializes the real fresh outer binder. -/
theorem initialized_typed (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (given : Metadata fixture) :
    StatementHasType (source fixture.packet.named) ⟨wordType, 0⟩ (runtimeContext fixture.packet)
      (statementId fixture.packet 0) (localContext fixture) letFacts := by
  apply StatementHasType.letInitialized (lookupStatement?_sound fixture.graph.initializedFound)
    fixture.graph.initializedForm
  · simpa only [given.scheme, TypeSystem.Scheme.mono, fixture.graph.lambdaType, functionType] using
      SourceCoreChosenOrdinaryAcceptedTyping.lambda_typed lambda
  · rw [given.scheme]; rfl
  · exact given.generalizes
  · exact given.extended
  · exact given.initializedType

/-- Both paired local tables hold the same genuine binder, instantiated with
one empty substitution and its empty requirement spine. -/
theorem Metadata.reference (given : Metadata fixture) :
    ReferenceUseValid (localContext fixture) (.local fixture.graph.binder.id) functionType [] := by
  refine .local (Context.localLookup_withLocal_self _ _ _ _)
    (Context.localSchemeRequirementsLookup_withLocal_self _ _ _ _) ?_
  refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ given.requirements) ?_ [] ?_ ?_ ?_ List.nodup_nil ?_ ?_
  · rw [given.scheme]
    exact SchemeWellFormed.monoAdmissible (function_admissible _ local_binders)
  · rw [given.scheme]
    exact ExactSubstitution.empty
  · intro metavariable replacement member
    cases member
  · rw [given.scheme]
    exact SchemeInstantiates.empty_apply functionType
  · intro id member
    cases member
  · simp only [instantiateLocalSchemePredicates, given.requirements, List.map_nil]
    exact .nil

theorem callee_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 9) functionType := by
  have admissible := function_admissible (localContext fixture) local_binders
  have typed : ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 9) fixture.graph.callee.type := by
    refine ExpressionHasType.intro (plan := .ordinary []) (lookupExpression?_sound fixture.graph.calleeFound)
      ?_ ?_ admissible ?_ ?_
    · rw [fixture.graph.calleeForm]
      exact .reference given.reference
    · simp only [ExpressionNode.rawType, fixture.parentRows.calleeCoercions, given.calleeType]
    · simpa only [given.calleeType] using admissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro id member; cases member
      · rw [given.calleeType, fixture.parentRows.calleeCoercions]; exact .nil _
      · simp only [fixture.parentRows.calleeRequirements, fixture.parentRows.calleeCoercions]
        rfl
  simpa only [given.calleeType] using typed

private theorem requirements_of_owned {node : ExpressionNode} {requirements : List RequirementId}
    (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements) :
    node.requirements = requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at owned
  rw [coercions] at owned
  change (if node.requirements.length < 0 then none else
    if node.requirements = node.requirements.take (node.requirements.length - 0) ++ [] then
      some (node.requirements.take (node.requirements.length - 0)) else none) = some requirements at owned
  simpa using owned

private theorem numeric_typed {packet : Packet} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {literal : Syntax.CoreLiteralValue} {value index : Nat}
    (rows : context.solvedRequirements = numericRows)
    (binders : TypeParameterBindersWellFormed context)
    (found : (source packet.named).lookupExpression? id = some node)
    (form : node.form = .integerLiteral literal (argumentResolution value index))
    (type : node.type = wordType) (coercions : node.coercions = [])
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [⟨index⟩])
    (denotes : NumericLiteralDenotes literal value) (member : index = 0 ∨ index = 1 ∨ index = 2) :
    ExpressionHasType (source packet.named) context id wordType := by
  have valid : IntegerLiteralValid context literal (argumentResolution value index) :=
    .word denotes rfl (numeric_requirement rows member)
  have admissible : TypeAdmissible context wordType := .word binders
  have typed : ExpressionHasType (source packet.named) context id node.type := by
    refine ExpressionHasType.intro (plan := .ordinary [⟨index⟩]) (lookupExpression?_sound found) ?_ ?_ admissible ?_ ?_
    · rw [form]; exact .integerLiteral valid
    · simp only [ExpressionNode.rawType, coercions, type]
    · simpa only [type] using admissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro requirement inList
        have same : requirement = ⟨index⟩ := List.mem_singleton.mp inList
        subst requirement
        exact ⟨_, numeric_requirement rows member⟩
      · rw [type, coercions]; exact .nil _
      · rw [requirements_of_owned coercions owned, coercions]
        rfl
  simpa only [type] using typed

theorem left_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 7) wordType :=
  numeric_typed fixture.runtime.rows local_binders fixture.parentRows.leftFound fixture.parentRows.leftForm
    given.leftType fixture.parentRows.leftCoercions fixture.parentRows.leftOwned
    (numericLiteralValue?_sound rfl) (Or.inr (Or.inl rfl))

theorem right_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 8) wordType :=
  numeric_typed fixture.runtime.rows local_binders fixture.parentRows.rightFound fixture.parentRows.rightForm
    given.rightType fixture.parentRows.rightCoercions fixture.parentRows.rightOwned
    (numericLiteralValue?_sound rfl) (Or.inr (Or.inr rfl))

/-- The one physical argument is the actual pair expression. -/
theorem argument_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 6) parameterType := by
  have admissible : TypeAdmissible (localContext fixture) parameterType := .product (.word local_binders) (.word local_binders)
  have typed : ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 6) fixture.graph.argument.type := by
    refine ExpressionHasType.intro (plan := .ordinary []) (lookupExpression?_sound fixture.graph.argumentFound)
      ?_ ?_ admissible ?_ ?_
    · rw [fixture.graph.argumentForm]
      exact .tuple (.cons (left_typed given) (.cons (right_typed given) (.nil _)))
    · simp only [ExpressionNode.rawType, fixture.parentRows.argumentCoercions, given.argumentType]
    · simpa only [given.argumentType] using admissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro id member; cases member
      · rw [given.argumentType, fixture.parentRows.argumentCoercions]; exact .nil _
      · simp only [fixture.parentRows.argumentRequirements, fixture.parentRows.argumentCoercions]
        rfl
  simpa only [given.argumentType] using typed

theorem indirect_application : IndirectApplicationValid (localContext fixture) indirectMetadata [parameterType] parameterType :=
  .intro rfl rfl rfl (.nil _)

/-- Callee typing, the physical singleton argument and its actual metadata
construct the raw indirect-call judgment; no Core read is inverted. -/
theorem parent_typed (given : Metadata fixture) :
    ExpressionHasType (source fixture.packet.named) (localContext fixture) (expressionId fixture.packet 5) wordType := by
  have admissible : TypeAdmissible (localContext fixture) wordType := .word local_binders
  have typed : ExpressionHasType (source fixture.packet.named) (localContext fixture)
      (expressionId fixture.packet 5) fixture.graph.parent.type := by
    refine ExpressionHasType.intro (plan := .indirectCall []) (lookupExpression?_sound fixture.graph.parentFound)
      ?_ ?_ admissible ?_ ?_
    · rw [fixture.graph.parentForm]
      exact .indirectCall (callee_typed given) (.cons (argument_typed given) (.nil _)) indirect_application
    · simp only [ExpressionNode.rawType, fixture.graph.parentCoercions, fixture.graph.parentType]
    · simpa only [fixture.graph.parentType] using admissible
    · apply ExpressionRequirementPlan.Valid.indirectCall
      · intro id member; cases member
      · rw [fixture.graph.parentType, fixture.graph.parentCoercions]; exact .nil _
      · simp only [fixture.graph.parentRequirements, fixture.graph.parentCoercions]
        rfl
  simpa only [fixture.graph.parentType] using typed

def returnFacts : StatementFacts := {
  type := wordType, hasValue := true, sawReturn := true, control := .returned }

theorem returned_typed (given : Metadata fixture) :
    StatementHasType (source fixture.packet.named) ⟨wordType, 0⟩ (localContext fixture)
      (statementId fixture.packet 4) (localContext fixture) returnFacts :=
  .returnValue (lookupStatement?_sound fixture.graph.outerReturnFound) fixture.graph.outerReturnForm
    (parent_typed given) given.returnedType

def bodyFacts : BodyFacts := .cons letFacts (.singleton returnFacts)

theorem body_typed (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture) (given : Metadata fixture) :
    StatementsHaveType (source fixture.packet.named) ⟨wordType, 0⟩ (runtimeContext fixture.packet)
      [statementId fixture.packet 0, statementId fixture.packet 4] (localContext fixture) bodyFacts :=
  .cons (initialized_typed lambda given) (.singleton (returned_typed given))

theorem body_completes : BodyCompletes wordType bodyFacts :=
  ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The actual public Header's inferred Source result and body context are
identified by its retained view and the checked original result field. -/
theorem Metadata.header_result (given : Metadata fixture)
    {header : SourceCoreChosenOrdinaryAcceptedHeader.ActualHeader fixture}
    (atHeader : SourceCoreChosenOrdinaryAcceptedHeader.HeaderAt fixture header) :
    header.function.resultType = wordType := by
  have result : header.function.resultType = fixture.packet.named.specialized.function.inferredBodyType := by
    simpa only [atHeader.named] using header.agreement.result
  exact result.trans given.resultType

theorem header_body_typed (lambda : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (given : Metadata fixture) {header : SourceCoreChosenOrdinaryAcceptedHeader.ActualHeader fixture}
    (atHeader : SourceCoreChosenOrdinaryAcceptedHeader.HeaderAt fixture header) :
    StatementsHaveType header.function.source ⟨header.function.resultType, 0⟩ header.function.context
      header.function.body (localContext fixture) bodyFacts := by
  rw [atHeader.source, atHeader.functionContext, atHeader.statements, given.header_result atHeader]
  exact body_typed lambda given

theorem header_body_completes (given : Metadata fixture)
    {header : SourceCoreChosenOrdinaryAcceptedHeader.ActualHeader fixture}
    (atHeader : SourceCoreChosenOrdinaryAcceptedHeader.HeaderAt fixture header) :
    BodyCompletes header.function.resultType bodyFacts := by
  rw [given.header_result atHeader]
  exact body_completes

/-- Finite receipt execution is separate from Source/Core runtime equivalence. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match SourceCoreChosenOrdinaryAcceptedTyping.shape fixture, metadata fixture with
    | .ok _, .ok _ => IO.println "accepted outer Source typing: actual f binder, argument types and inferred Word result checked"
    | .error error, _ => throw (IO.userError error)
    | _, .error error => throw (IO.userError error)

end Tests.SourceCoreChosenOrdinaryAcceptedOuterTyping
