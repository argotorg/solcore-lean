import Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControlShape

/-! Function-mode fallthrough fixes the raw result annotation in the same
recursive guarded grammar. This follows from independent source control and
static tree shape, including at arbitrary nested loop depths. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionFallthrough
open Core Frontend SourceInference
open TypedScopedStatements (Executes source_view)

def FallthroughAt (source : TypedSource) (expected : TypeSystem.Ty)
    (mode : Bool) (statements : List StatementId) : Prop :=
  ∀ {program : Program} {actualContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment}
    {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap},
    ScalarStatementViews.ListExecutes mode program actualContext evidence source
      environment before statements finalContext (.fallthrough nextEnvironment) after →
    mode = false ∨ expected = .unit

variable {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
theorem lexical_fallthrough {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected mode statements := by
  induction tree with
  | nil allowed => exact fun _ => allowed
  | returnUnit => exact fun _ => .inr rfl
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ other; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | tail found form expressionFound valueType value =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    cases executed with
    | singleton contains notTail head =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
      subst_vars
      exact False.elim (notTail _ form)
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

theorem assignment_fallthrough {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : ProtectedLexicalAssignments.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected mode statements := by
  induction tree with
  | lexical fragment => exact lexical_fallthrough fragment unique
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
  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head errors remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal

theorem loop_fallthrough {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : ProtectedLoopStatements.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected mode statements := by
  induction tree with
  | lexical fragment => exact assignment_fallthrough fragment unique
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
  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head errors remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
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

theorem true_fallthrough_unit {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : ProtectedLoopStatements.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope true statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment}
    {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    (trace : Executes true program actualContext evidence source environment before
      statements finalContext (.fallthrough nextEnvironment) after) : expected = .unit := by
  cases source_view trace with
  | control executed => exact (loop_fallthrough tree unique executed).resolve_left (by decide)

end Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionFallthrough
