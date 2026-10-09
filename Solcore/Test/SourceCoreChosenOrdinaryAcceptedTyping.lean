import Solcore.Test.SourceCoreChosenOrdinaryAcceptedFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts

/-! Finite checks on the unchanged accepted fixture supply the actual lambda
parameter and return rows. Declarative typing is then constructed from the
original numeric requirement and the genuine lexical extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedTyping
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture
open CallableIndexedNamedGeneration

/-- Each equation refers to an actual retained node or binder. -/
structure Shape (fixture : AcceptedFixture) where
  parameter : TypedBinder
  parameters : fixture.graph.parameters = [parameter]
  owned : parameter.id.owner = (source fixture.packet.named).owner
  scheme : parameter.scheme = .mono parameterType
  requirements : parameter.schemeRequirements = []
  ordinary : parameter.comptime = false
  notInput : (source fixture.packet.named).inputs.any
    (fun input => decide (input.id = parameter.id)) = false
  returnedType : fixture.graph.returned.type = wordType

/-- This check returns proofs of the actual finite shape, without changing
any Source row or using a checker-soundness assumption. -/
def shape (fixture : AcceptedFixture) : Except String (Shape fixture) :=
  match parameters : fixture.graph.parameters with
  | [parameter] =>
    if correct : parameter.id.owner = (source fixture.packet.named).owner ∧
        parameter.scheme = .mono parameterType ∧ parameter.schemeRequirements = [] ∧
        parameter.comptime = false ∧
        (source fixture.packet.named).inputs.any (fun input => decide (input.id = parameter.id)) = false ∧
        fixture.graph.returned.type = wordType then
      .ok ⟨parameter, parameters, correct.1, correct.2.1, correct.2.2.1,
        correct.2.2.2.1, correct.2.2.2.2.1, correct.2.2.2.2.2⟩
    else .error "actual lambda parameter or return type differs"
  | _ => .error "actual lambda parameter count differs"

variable {fixture : AcceptedFixture}

def Shape.bodyContext (given : Shape fixture) : SourceSemantics.Context :=
  (runtimeContext fixture.packet).withLocal given.parameter.id
    given.parameter.scheme given.parameter.schemeRequirements

theorem initial_binders : TypeParameterBindersWellFormed (runtimeContext fixture.packet) := by
  constructor
  · exact List.nodup_nil
  · intro parameter member
    cases member

theorem Shape.body_binders (given : Shape fixture) :
    TypeParameterBindersWellFormed given.bodyContext := initial_binders

theorem Shape.fresh (given : Shape fixture) :
    LocalFresh (runtimeContext fixture.packet) given.parameter.id := by
  constructor <;> exact List.not_mem_nil

/-- The actual monomorphic parameter extends the exact fixture context. -/
theorem Shape.parameters_extend (given : Shape fixture) :
    MonoBindersExtend (source fixture.packet.named).owner (runtimeContext fixture.packet)
      fixture.graph.parameters [parameterType] given.bodyContext := by
  rw [given.parameters]
  refine .cons given.scheme (.intro ?_ given.fresh) (.nil _)
  refine ⟨given.owned, ?_, ?_, fun _ => given.requirements⟩
  · rw [given.scheme]
    exact ⟨initial_binders, List.nodup_nil, .product (.builtin .word) (.builtin .word)⟩
  · rw [given.scheme]
    intro metavariable member
    cases member

/-- Requirement zero is the original solved numeric row in the same body
context; extending a lexical binder does not replace the ledger. -/
theorem Shape.literal_valid (given : Shape fixture) :
    IntegerLiteralValid given.bodyContext (.decimal "7") literalResolution := by
  refine .word (numericLiteralValue?_sound rfl) rfl ?_
  apply numeric_requirement (context := given.bodyContext)
  · exact fixture.runtime.rows
  · exact Or.inl rfl

/-- The genuine literal occurrence is typed with its original requirement. -/
theorem literal_typed (given : Shape fixture) :
    ExpressionHasType (source fixture.packet.named) given.bodyContext
      (expressionId fixture.packet 3) wordType := by
  have valid : TypeAdmissible given.bodyContext wordType := .word given.body_binders
  have typed : ExpressionHasType (source fixture.packet.named) given.bodyContext
      (expressionId fixture.packet 3) fixture.graph.literal.type := by
    refine ExpressionHasType.intro (plan := .ordinary [⟨0⟩]) (lookupExpression?_sound fixture.graph.literalFound) ?_ ?_ valid ?_ ?_
    · rw [fixture.graph.literalForm]
      exact .integerLiteral given.literal_valid
    · simp only [ExpressionNode.rawType, fixture.graph.literalCoercions, fixture.graph.literalType]
    · simpa only [fixture.graph.literalType] using valid
    · apply ExpressionRequirementPlan.Valid.ordinary
      · intro id member
        have same : id = ⟨0⟩ := List.mem_singleton.mp member
        subst id
        exact ⟨_, numeric_requirement fixture.runtime.rows (Or.inl rfl)⟩
      · rw [fixture.graph.literalType, fixture.graph.literalCoercions]
        exact .nil _
      · simp only [fixture.graph.literalRequirements, fixture.graph.literalCoercions]
        rfl
  simpa only [fixture.graph.literalType] using typed

def returnFacts : StatementFacts := {
  type := wordType, hasValue := true, sawReturn := true, control := .returned }

/-- The real return row uses the literal derivation at the installed body
context and the checked return node type. -/
theorem return_typed (given : Shape fixture) :
    StatementHasType (source fixture.packet.named) ⟨wordType, 0⟩ given.bodyContext
      (statementId fixture.packet 2) given.bodyContext returnFacts :=
  .returnValue (lookupStatement?_sound fixture.graph.returnedFound)
    fixture.graph.returnedForm (literal_typed given) given.returnedType

theorem body_typed (given : Shape fixture) :
    StatementsHaveType (source fixture.packet.named) ⟨wordType, 0⟩ given.bodyContext
      [statementId fixture.packet 2] given.bodyContext (BodyFacts.singleton returnFacts) :=
  .singleton (return_typed given)

theorem body_completes : BodyCompletes wordType (BodyFacts.singleton returnFacts) := by
  exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The actual lambda judgment is built from its genuine binder extension
and singleton return, at the original runtime context. -/
theorem lambda_typed (given : Shape fixture) :
    ExpressionHasType (source fixture.packet.named) (runtimeContext fixture.packet)
      (expressionId fixture.packet 1) fixture.graph.lambdaNode.type := by
  have word : TypeAdmissible (runtimeContext fixture.packet) wordType := .word initial_binders
  have function : TypeAdmissible (runtimeContext fixture.packet) (.function parameterType wordType) :=
    .function (.product word word) word
  refine ExpressionHasType.intro (plan := .ordinary []) (lookupExpression?_sound fixture.graph.lambdaFound) ?_ ?_ function ?_ ?_
  · rw [fixture.graph.lambdaForm]
    apply ExpressionFormHasRawType.lambda (parameterTypes := [parameterType])
    · rw [given.parameters]
      simp
    · exact given.parameters_extend
    · exact body_typed given
    · exact body_completes
  · simp only [ExpressionNode.rawType, fixture.graph.lambdaCoercions, fixture.graph.lambdaType]
  · simpa only [fixture.graph.lambdaType] using function
  · apply ExpressionRequirementPlan.Valid.ordinary
    · intro id member
      cases member
    · rw [fixture.graph.lambdaType, fixture.graph.lambdaCoercions]
      exact .nil _
    · simp only [fixture.graph.lambdaRequirements, fixture.graph.lambdaCoercions]
      rfl

/-- Raw lambda facts come from this actual typing judgment and the original
well-formed occurrence graph, independently of native compiler typing. -/
theorem source_facts (given : Shape fixture) :
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts
      (CallableIndexedLambdaGeneration.closure fixture.packet.named fixture.graph.parameters
        wordType [statementId fixture.packet 2] (runtimeContext fixture.packet) [] [])
      (expressionId fixture.packet 1) fixture.graph.lambdaNode := by
  exact CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique fixture.graph.lambdaFound
    fixture.graph.lambdaForm (lambda_typed given) fixture.graph.lambdaCoercions

/-- Execute the finite receipt check over the unchanged compiler fixture.
The declarative judgments above remain kernel proofs of those exact rows. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match shape fixture with
    | .error error => throw (IO.userError error)
    | .ok _ => IO.println "accepted lambda Source typing: actual monomorphic parameter and Word return checked"

end Tests.SourceCoreChosenOrdinaryAcceptedTyping
