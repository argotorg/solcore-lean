import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchControlShape

/-! The source function result annotation is fixed by actual successful
fallthrough in the recursive lexical, loop and match grammar. No source
execution is required in a static certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open TypedScopedStatements (Executes source_view)

/-- Initializer positions do not finish a function. A statement-list position
may fall through in function mode only with a raw Unit result annotation. -/
def FallthroughAt (source : TypedSource) (expected : TypeSystem.Ty) : Position → Prop
  | .initializers _ _ _ _ => True
  | .statements mode statements =>
      ∀ {program : Program} {actualContext finalContext : SourceSemantics.Context}
        {evidence : Dynamic.EvidenceEnvironment}
        {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap},
        ScalarStatementViews.ListExecutes mode program actualContext evidence source
          environment before statements finalContext (.fallthrough nextEnvironment) after →
        mode = false ∨ expected = .unit

variable {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem Tree.fallthrough_at {context : SourceSemantics.Context} {scope : Scope}
    {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative
      context scope position expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected position := by
  induction tree with
  | body syntaxTree _ =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    cases GenericLexicalStatements.syntax_control_shape syntaxTree unique executed with
    | fallthrough _ allowed => exact allowed
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @breaking context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, tail⟩ | ⟨_, terminal⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | @continuing context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, tail⟩ | ⟨_, terminal⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode code reason found form conditionFound conditionType typed loopBody nativeTyped remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched code selfReason control caseFacts
      found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator
      requests receipt ordinary children remaining childIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · cases GenericLexicalStatements.block_terminates exactUnique found form stops head
    · cases terminal
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType typed thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · cases GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops head
    · cases terminal
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued childIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · cases ReachableMatchContinuations.DefaultStopped.terminates exactUnique stops head
    · cases terminal

  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard | initializerAssign | initializerBitNot =>
    trivial

theorem Tree.true_fallthrough_unit {context : SourceSemantics.Context} {scope : Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative
      context scope (.statements true statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment}
    {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    (trace : Executes true program actualContext evidence source environment before
      statements finalContext (.fallthrough nextEnvironment) after) : expected = .unit := by
  cases source_view trace with
  | control executed => exact (tree.fallthrough_at unique executed).resolve_left (by decide)

end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
