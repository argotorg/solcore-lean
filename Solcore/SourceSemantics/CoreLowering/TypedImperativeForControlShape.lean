import Solcore.SourceSemantics.CoreLowering.TypedImperativeForTree
import Solcore.SourceSemantics.CoreLowering.ForSourceInduction
import Solcore.SourceSemantics.CoreLowering.ForSourceViews

/-! Successful source control excludes the separate fault judgment for this
recursive grammar, including ordinary assignment heads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
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

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem Tree.control_shapeAt {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope position expected type code)
    (unique : NodeOccurrencesUnique source) : ControlShapeAt source position := by
  induction tree with
  | body syntaxTree _ =>
    intro program actualContext finalContext evidence environment before after outcome executed
    cases TypedLexicalNamedBody.syntax_control_shape syntaxTree unique executed with
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
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard | initializerAssign | initializerBitNot => trivial

theorem Tree.control_shape {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope (.statements mode statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after) :
    ControlShape outcome := tree.control_shapeAt unique executed

theorem Tree.control_not_fault {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope (.statements mode statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext (.fault reason) after) : False := by
  cases tree.control_shape unique executed
end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
