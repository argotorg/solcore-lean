import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.ForSourceInduction
import Solcore.SourceSemantics.CoreLowering.ForSourceViews

/-! Successful source control excludes the separate fault judgment for this
recursive grammar, including ordinary assignment heads and selected match bodies.
Static arm context receipts are kept separate from the arbitrary actual context
of each independent success derivation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open TypedLexicalWhile (ControlShape while_control_shape)

theorem for_control_shape {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
    {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after) :
    (∃ next, outcome = .fallthrough next) ∨ (∃ value, outcome = .returned value) := by
  apply LoopStatements.for_induction
    (motive := fun _ _ _ _ _ _ _ _ _ outcome _ =>
      (∃ next, outcome = .fallthrough next) ∨ (∃ value, outcome = .returned value))
    (execution := trace)
  · intros; exact .inl ⟨_, rfl⟩
  · intros; assumption
  · intros; assumption
  · intros; exact .inl ⟨_, rfl⟩
  · intros; exact .inr ⟨_, rfl⟩

def ControlShapeAt (source : TypedSource) : Position → Prop
  | .initializers _ _ _ _ => True
  | .statements mode statements =>
      ∀ {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome},
        ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after →
        ControlShape outcome


private theorem selected_arm_body {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm statements bindings)) :
    ∃ arm ∈ cases, statements = arm.body := by
  cases selected with
  | head => exact ⟨_, List.mem_cons_self, rfl⟩
  | tail _ next =>
    obtain ⟨arm, member, same⟩ := selected_arm_body next
    exact ⟨arm, List.mem_cons_of_mem _ member, same⟩
termination_by cases.length

private theorem selected_default {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact selected_default next
termination_by cases.length

/-- Every source arm has an actual retained compiler request and a context
from its independent typing. Runtime selected bindings are not used to infer
this static context. Duplicate body lists may retain several such requests. -/
private theorem arm_request
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {site : StatementId}
    {scope : Scope} {expected : TypeSystem.Ty} {cases : List TypedMatchCase} {nativeArms : List (SourceCoreCompatibleDataMatches.Pattern × Expr)}
    {requests : List GenericMatchChildren.Request} {control : ControlContext} {parent : SourceSemantics.Context}
    {facts : List BodyFacts} {fallback : Option (List StatementId)} {wanted : TypedMatchCase}
    (certified : CompatibleMatchCertificates.Arms compilation source site scope expected
      (GenericMatchChildren.Occurs requests) cases nativeArms)
    (typed : MatchCasesHaveType source control parent expected cases facts)
    (member : wanted ∈ cases) :
    ∃ request childContext, request ∈ requests ∧ request.statements = wanted.body ∧
      GenericMatchChildren.ScopedContextFor source parent (scope.map Prod.fst) expected cases fallback request childContext := by
  induction certified generalizing facts with
  | nil => cases member
  | @cons arm rest pattern code nativeArms patternCertificate matcher body tail ih =>
    cases typed with
    | cons head typedTail =>
      cases member with
      | head =>
        cases head with
        | intro patternTyped extended _ =>
          exact ⟨⟨_, wanted.body, code⟩, _, body, rfl,
            GenericMatchChildren.ScopedContextFor.compiled_arm_ids code List.mem_cons_self patternCertificate patternTyped extended⟩
      | tail _ member =>
        obtain ⟨request, childContext, retained, sameBody, context⟩ := ih typedTail member
        refine ⟨request, childContext, retained, sameBody, ?_⟩
        cases context with
        | arm member same typed extended ids => exact .arm (List.mem_cons_of_mem _ member) same typed extended ids
        | default same ids => exact .default same ids

/-- Success control only uses genuine success derivations of the selected
body. Fault judgments remain separate and cannot satisfy this premise. -/
private theorem match_control_shape
    {program : Program} {actualContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {resolution : MatchResolution}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .matchWith resolution)
    (arms : ∀ arm, arm ∈ resolution.cases → ControlShapeAt source (.statements false arm.body))
    (fallback : ∀ statements, resolution.defaultBody = some statements →
      ControlShapeAt source (.statements false statements))
    (executed : Dynamic.StatementExecutes program actualContext evidence source environment before id finalContext outcome after) :
    ControlShape outcome := by
  have shapes : ∀ other, ContainsStatement source id other → other.form = .matchWith resolution := by
    intro other otherContains
    have same : other = node := Option.some.inj
      ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
    exact same ▸ form
  clear contains form
  cases executed <;> have actualForm := shapes _ (by assumption) <;> simp_all
  · obtain ⟨arm, member, same⟩ := selected_arm_body (by assumption)
    cases same
    exact (arms arm member (by assumption)).restore environment
  · exact (fallback _ (selected_default (by assumption)) (by assumption)).restore environment
  · exact .fallthrough environment

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem Tree.control_shapeAt {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code)
    (unique : NodeOccurrencesUnique source) : ControlShapeAt source position := by
  induction tree with
  | body syntaxTree _ =>
    intro program actualContext finalContext evidence environment before after outcome executed
    cases GenericLexicalStatements.syntax_control_shape syntaxTree unique executed with
    | fallthrough next _ => exact .fallthrough next
    | returned value => exact .returned value
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, rfl, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, _, _, rfl, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact (innerIH innerTrace).restore environment
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact (elseIH branchTrace).restore environment
      | true => exact (thenIH branchTrace).restore environment
  | @breaking context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.breaking unique contains form head; exact .breaking environment
  | @continuing context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.continuing unique contains form head; exact .continuing environment
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode code reason found form conditionFound conditionType typed loopBody nativeTyped remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.whileLoop unique contains form head
      rcases while_control_shape innerTrace with ⟨next, rfl⟩ | ⟨value, rfl⟩
      · exact .fallthrough environment
      · exact .returned value

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨first, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique contains form first
      cases terminal
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨first, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _⟩ := CompatibleBitNotStatements.bitNot_view unique contains form first
      cases terminal
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, _, _, _, innerOutcome, rfl, _, loop⟩ := ForSourceViews.success unique contains form head
      rcases for_control_shape loop with ⟨next, rfl⟩ | ⟨value, rfl⟩
      · exact .fallthrough environment
      · exact .returned value

  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched code selfReason control caseFacts
      found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator
      requests receipt ordinary children remaining childIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · apply match_control_shape unique contains form _ _ head
      · intro arm member
        cases receipt with
        | @matchWith certificateNode statementType childNode payload scrutinee nativeArms fallback branches code
            read allowed sourceForm requirements hiddenOwned hiddenFresh scrutineeOwned childFound projection
            expression sameType armCertificates fallbackCertificate branchCertificates hiddenCompiled =>
          have sameNode : childNode = scrutineeNode := Option.some.inj (childFound.symm.trans scrutineeFound)
          subst childNode
          obtain ⟨request, childContext, retained, sameBody, selectedContext⟩ := arm_request armCertificates casesTyped member
          have shape : ControlShapeAt source (.statements false request.statements) :=
            childIH request retained childContext selectedContext
          rw [← sameBody]
          exact @shape
      · intro statements selected
        cases receipt with
        | matchWith read allowed sourceForm requirements hiddenOwned hiddenFresh scrutineeOwned childFound projection
            expression sameType armCertificates fallbackCertificate branchCertificates hiddenCompiled =>
          rw [selected] at fallbackCertificate
          cases fallbackCertificate with
          | some certified =>
            exact childIH ⟨_, statements, _⟩ certified context (.default selected rfl)
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, terminal⟩
    · cases GenericLexicalStatements.block_terminates exactUnique found form stops head
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact (innerIH innerTrace).restore environment
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType typed thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, terminal⟩
    · cases GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops head
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact (elseIH branchTrace).restore environment
      | true => exact (thenIH branchTrace).restore environment
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts
      exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator
      requests receipt ordinary children stops issued childIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, terminal⟩
    · cases ReachableMatchContinuations.DefaultStopped.terminates exactUnique stops head
    · apply match_control_shape unique contains form _ _ head
      · intro arm member
        cases receipt with
        | @matchWith certificateNode statementType childNode payload scrutinee nativeArms fallback branches code
            read allowed sourceForm requirements hiddenOwned hiddenFresh scrutineeOwned childFound projection
            expression sameType armCertificates fallbackCertificate branchCertificates hiddenCompiled =>
          have sameNode : childNode = scrutineeNode := Option.some.inj (childFound.symm.trans scrutineeFound)
          subst childNode
          obtain ⟨request, childContext, retained, sameBody, selectedContext⟩ := arm_request armCertificates casesTyped member
          have shape : ControlShapeAt source (.statements false request.statements) :=
            childIH request retained childContext selectedContext
          rw [← sameBody]
          exact @shape
      · intro statements selected
        cases receipt with
        | matchWith read allowed sourceForm requirements hiddenOwned hiddenFresh scrutineeOwned childFound projection
            expression sameType armCertificates fallbackCertificate branchCertificates hiddenCompiled =>
          rw [selected] at fallbackCertificate
          cases fallbackCertificate with
          | some certified =>
            exact childIH ⟨_, statements, _⟩ certified context (.default selected rfl)

  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard | initializerAssign | initializerBitNot => trivial

theorem Tree.control_shape {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after) :
    ControlShape outcome := tree.control_shapeAt unique executed

theorem Tree.control_not_fault {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext (.fault reason) after) : False := by
  cases tree.control_shape unique executed
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
