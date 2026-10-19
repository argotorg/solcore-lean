import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion

/-! The ordinary Source declaration captures one principal descriptor and
allocates it once. Its compiler-supported direct lambda excludes the genuine
unsupported-initializer fault without evaluating the initializer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPlainInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds

variable {program : Program} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem selected (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {other}
    (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

theorem value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ function location, size = SourceExecutionSize.stepSize [] ∧ finalContext = nextContext ∧
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.GeneralizedClosureCaptures context source environment binder initializer function ∧
      Dynamic.Heap.AllocatesGeneralized before function location after := by
  cases trace <;> have same := selected unique found (by assumption) <;> subst_vars <;> simp_all
  rename_i captures _ extension allocated
  have equal := Dynamic.BinderExtends.functional extended extension
  exact ⟨equal.symm, _, captures, allocated⟩

theorem fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (capturable : ∃ function, Dynamic.GeneralizedClosureCaptures context source environment binder initializer function)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) : False := by
  cases trace
  case missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  all_goals have same := selected unique found (by assumption)
  all_goals subst_vars
  all_goals simp_all
  rename_i equal _ unsupported _
  obtain ⟨rfl, rfl⟩ := equal
  obtain ⟨function, captures⟩ := capturable
  exact Dynamic.GeneralizedInitializerUnsupported.not_captures unsupported captures

private theorem empty_trace {mode : Bool} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} :
    PlainStatements program mode (SourceExecutionSize.stepSize []) invocation context environment heap
      [] context (.fallthrough environment) heap := by
  cases mode <;> exact .control .nil

theorem generalized {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (capturable : ∃ function, Dynamic.GeneralizedClosureCaptures context invocation.source environment binder initializer function)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize function location bound,
      tailSize < size ∧ Dynamic.GeneralizedClosureCaptures context invocation.source environment binder initializer function ∧
      Dynamic.Heap.AllocatesGeneralized before function location bound ∧
      PlainStatements program mode tailSize invocation nextContext ((binder.id, location) :: environment)
        bound rest finalContext outcome after := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, _, _, _, _, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, _, tailStrict, head, tail⟩
  · exact (fault unique found form polymorphic capturable failed).elim
  · obtain ⟨function, location, rfl, equalContext, equalOutcome, captures, allocated⟩ :=
      value unique found form polymorphic extended head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · exact ⟨SourceExecutionSize.stepSize [], function, location, after, strict, captures, allocated, empty_trace⟩
  · obtain ⟨function, location, _, equalContext, equalOutcome, captures, allocated⟩ :=
      value unique found form polymorphic extended head
    subst middleContext
    cases equalOutcome
    exact ⟨tailSize, function, location, middle, tailStrict, captures, allocated, tail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPlainInversion
