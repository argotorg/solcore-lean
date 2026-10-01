import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementMeaning
import Solcore.SourceSemantics.CoreLowering.FunctionCalls

/-! The static body receipt discharges ordinary body correspondence at its
actual context. Independent closure-call traces and language-result values are
connected without assuming a universal body theorem for arbitrary contexts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

/-- Function call exits, including the independent escaped-control fault. -/
inductive Exit (resultType : TypeSystem.Ty) : Dynamic.ControlOutcome → Dynamic.ExpressionOutcome → Prop where
  | returned (value : Dynamic.Value) : Exit resultType (.returned value) (.value value)
  | unit (environment : Dynamic.Environment) (same : resultType = .unit) :
      Exit resultType (.fallthrough environment) (.value .unit)
  | fault (reason : Dynamic.SemanticFault) : Exit resultType (.fault reason) (.fault reason)
  | breaking (environment : Dynamic.Environment) :
      Exit resultType (.breaking environment) (.fault .controlEscapedFunction)
  | continuing (environment : Dynamic.Environment) :
      Exit resultType (.continuing environment) (.fault .controlEscapedFunction)

theorem trace_control {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ finalContext control,
      Dynamic.FunctionStatementsExecuteOutcome program context function.evidence function.source environment
        before function.body finalContext control after ∧ Exit function.resultType control outcome := by
  cases trace with
  | returned execution => exact ⟨_, _, .control execution, .returned _⟩
  | unit same execution => exact ⟨_, _, .control execution, .unit _ same⟩
  | fault execution => exact ⟨_, _, .fault execution, .fault _⟩
  | escaped execution escape =>
    rcases escape with ⟨environment, rfl⟩ | ⟨environment, rfl⟩
    · exact ⟨_, _, .control execution, .breaking environment⟩
    · exact ⟨_, _, .control execution, .continuing environment⟩

theorem body_result {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {expected : TypeSystem.Ty} {type : Ty} {control : Dynamic.ControlOutcome}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type control value)
    (exit : Exit expected control outcome) :
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world expected type faults outcome value := by
  cases related with
  | fallthrough environment => cases exit; exact .value .unit
  | returned payload => cases exit; exact .value payload
  | fault matched => cases exit; exact .fault matched

/-- The fixed grammar cannot manufacture fault control through successful
source execution. Actual source faults retain their separate fault derivation. -/
theorem tree_control_not_fault {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : CompatibleStatements.Tree readFuel values source context solved reasonAt scope statements expected type flow)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : Dynamic.FunctionStatementsExecute program actualContext evidence source environment before
      statements finalContext (.fault reason) after) : False := by
  induction tree generalizing actualContext finalContext environment before after with
  | nil => cases executed
  | @returnUnit id node rest found form =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
  | @returnValue id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
  | tail found form expressionFound valueType value =>
    cases executed with
    | singleton contains notTail head =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
      subst_vars
      exact notTail _ form
  | @discard id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih =>
    have contains := lookupStatement?_sound found
    have notTailExpression : true = true → rest = [] → ∀ other, node.form ≠ .expression other false := by
      intro _ empty other impossible
      rw [form] at impossible
      cases impossible
      simp [empty] at notTail
    rcases ScalarStatementViews.cons_view true unique contains notTailExpression executed with
      ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨rfl, same, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact ih tail
    · obtain ⟨_, impossible, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases impossible

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension contextValid unique uninitialized in
theorem Certificate.preserves
    (certificate : Certificate readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨_, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨_, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    certificate.tree.body_preserves functions extension program function.evidence contextValid unique uninitialized
      fellThrough escaped environments heaps locals agrees sourceTrace
  rw [← certificate.emitted] at evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, body_result represented exit,
    finalHeaps, maps, worlds, frame, metadata⟩

include extension contextValid unique uninitialized in
theorem Certificate.reflects
    (certificate : Certificate readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rw [certificate.emitted] at evaluated
  obtain ⟨control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    certificate.tree.body_reflects functions extension program function.evidence contextValid uninitialized
      fellThrough escaped environments heaps locals agrees evaluated
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value := by
    generalize raw : function.resultType = expected at represented
    cases represented with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact .value .unit
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact .value payload
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (tree_control_not_fault certificate.tree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched⟩
  obtain ⟨outcome, trace, result⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
