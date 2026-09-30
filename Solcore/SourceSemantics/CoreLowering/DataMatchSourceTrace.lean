import Solcore.SourceSemantics.CoreLowering.GenericMatchSelectedPrefix

/-! Views of finite independent match execution. They retain the actual source
scrutinee and body derivations, hidden-cell allocation and lexical scope. The
view is proved from the existing judgments; it is not an executable evaluator. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace
open Frontend Frontend.SourceInference

inductive Trace (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (resolution : MatchResolution) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | scrutineeFault {reason after}
      (fault : Dynamic.ExpressionFaults program context evidence source environment before resolution.scrutinee reason after) :
      Trace program context evidence source environment before resolution (.fault reason) after
  | patternFault {node value middle hidden location}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (allocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (fault : Dynamic.MatchCasesPatternFault context value resolution.cases) :
      Trace program context evidence source environment before resolution (.fault .invalidPattern) hidden
  | arm {node value middle hidden location statements bindings armContext armEnvironment bound finalContext outcome after}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
      (extended : BindersExtend source.owner context (bindings.map Prod.fst) armContext)
      (allocated : Dynamic.BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
      (body : Dynamic.StatementsExecuteOutcome program armContext evidence source armEnvironment bound statements finalContext outcome after) :
      Trace program context evidence source environment before resolution (Dynamic.restoreControl environment outcome) after
  | default {node value middle hidden location statements finalContext outcome after}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
      (body : Dynamic.StatementsExecuteOutcome program context evidence source environment hidden statements finalContext outcome after) :
      Trace program context evidence source environment before resolution (Dynamic.restoreControl environment outcome) after
  | noBranch {node value middle hidden location}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
      Trace program context evidence source environment before resolution (.fallthrough environment) hidden

private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

theorem of_outcome {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .matchWith resolution)
    (executed : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ Trace program context evidence source environment before resolution outcome after := by
  have formShape := shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases executed with
  | control executed =>
    cases executed <;> have actualForm := formShape _ (by assumption) <;> simp_all
    · exact .arm (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (.control (by assumption))
    · exact .default (by assumption) (by assumption) (by assumption) (by assumption) (.control (by assumption))
    · exact .noBranch (by assumption) (by assumption) (by assumption) (by assumption)
  | fault fault =>
    refine ⟨rfl, ?_⟩
    cases fault
    all_goals first
      | exact False.elim (present (by assumption))
      | have actualForm := formShape _ (by assumption); simp_all
    · exact .scrutineeFault (by assumption)
    · exact .patternFault (by assumption) (by assumption) (by assumption) (by assumption)
    · exact .arm (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (.fault (by assumption))
    · exact .default (by assumption) (by assumption) (by assumption) (by assumption) (.fault (by assumption))

theorem Trace.statement {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .matchWith resolution)
    (trace : Trace program context evidence source environment before resolution outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after := by
  cases trace with
  | scrutineeFault fault => exact .fault (.matchScrutinee contains form fault)
  | patternFault found evaluated allocated fault => exact .fault (.matchPattern contains form found evaluated allocated fault)
  | arm found evaluated hidden selected extended allocated body =>
    cases body with
    | control executed => exact .control (.matchArm contains form found evaluated hidden selected rfl rfl extended allocated executed)
    | fault fault => exact .fault (.matchArmBody contains form found evaluated hidden selected rfl rfl extended allocated fault)
  | default found evaluated hidden selected body =>
    cases body with
    | control executed => exact .control (.matchDefault contains form found evaluated hidden selected executed)
    | fault fault => exact .fault (.matchDefaultBody contains form found evaluated hidden selected fault)
  | noBranch found evaluated hidden selected => exact .control (.matchNoBranch contains form found evaluated hidden selected)

end Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace
