import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyCertificates
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlMeaning
import Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyMeaning

/-! Named-body correspondence for actual lexical scoped lowering. Static syntax
closes the function-mode fallthrough annotation and successful-control shape;
the concrete tree closes all expression and scoped children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleNamedBody (trace_control body_result)
open TypedScopedStatements (Executes source_view)

/-- The ordinary lexical grammar has only successful return or fallthrough.
Function-mode fallthrough carries its independent source Unit annotation. -/
inductive ControlShape (mode : Bool) (expected : TypeSystem.Ty) : Dynamic.ControlOutcome → Prop where
  | fallthrough (environment : Dynamic.Environment) (allowed : mode = false ∨ expected = .unit) :
      ControlShape mode expected (.fallthrough environment)
  | returned (value : Dynamic.Value) : ControlShape mode expected (.returned value)

private theorem restored_terminal {mode : Bool} {expected : TypeSystem.Ty}
    {environment : Dynamic.Environment} {outcome : Dynamic.ControlOutcome}
    (shape : ControlShape false expected outcome)
    (terminal : Dynamic.TerminalControl (Dynamic.restoreControl environment outcome)) :
    ControlShape mode expected (Dynamic.restoreControl environment outcome) := by
  cases shape with
  | fallthrough => cases terminal
  | returned value => exact .returned value

private theorem scoped_control_shape {source : TypedSource} {context : SourceSemantics.Context}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : TypedScopedStatements.Syntax source context mode statements expected)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before
      statements finalContext outcome after) : ControlShape mode expected outcome := by
  induction syntaxTree generalizing actualContext finalContext environment before after outcome with
  | nil allowed =>
    obtain ⟨_, rfl, _⟩ := ScalarStatementViews.nil_view _ executed
    exact .fallthrough _ allowed
  | @returnUnit mode id node rest found form sourceType =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      exact .returned _
  | @returnValue mode id node expression expressionNode expected rest found form sourceType expressionFound valueType typed value =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ other; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
    · obtain ⟨_, value, rfl, _⟩ := ScalarStatementViews.returnValue unique contains form head
      exact .returned value
  | tail found form sourceType expressionFound valueType typed value =>
    cases executed with
    | tailExpression => exact .returned _
    | singleton contains notTail head =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
      subst_vars
      exact False.elim (notTail _ form)
  | @discard mode id node expression expressionNode semicolon rest expected found form guard sourceType expressionFound typed value remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal

/-- This is a syntax inversion over the independent successful source judgment,
not a semantic assumption supplied by a caller. It also handles false-mode
scoped children whose enclosing result type may be non-Unit. -/
theorem syntax_control_shape {source : TypedSource} {context : SourceSemantics.Context}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : TypedLexicalControl.Syntax source context mode statements expected)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before
      statements finalContext outcome after) : ControlShape mode expected outcome := by
  induction syntaxTree generalizing actualContext finalContext environment before after outcome with
  | body body => exact scoped_control_shape body unique executed
  | @uninitialized context nextContext mode id node binder rest expected found form declaration mono extended ordinary remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, rfl, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases terminal
  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initialFound sourceType typed initial remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, _, _, rfl, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases terminal
  | @discard context mode id node expression expressionNode semicolon rest expected found form guard sourceType expressionFound typed value remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact restored_terminal (innerIH innerTrace) terminal
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact restored_terminal (elseIH branchTrace) terminal
      | true => exact restored_terminal (thenIH branchTrace) terminal

/-- The actual function-mode source fallthrough fixes the raw result annotation.
The separate original projection receipt subsequently fixes its native type. -/
theorem true_fallthrough_unit {source : TypedSource} {context : SourceSemantics.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : TypedLexicalControl.Syntax source context true statements expected)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    (trace : Executes true program actualContext evidence source environment before
      statements finalContext (.fallthrough nextEnvironment) after) : expected = .unit := by
  cases source_view trace with
  | control executed =>
    cases syntax_control_shape syntaxTree unique executed with
    | fallthrough _ allowed => exact allowed.resolve_left (by decide)

/-- A successful ordinary source-control derivation cannot masquerade as its
separate language-fault judgment, including through nested lexical scopes. -/
theorem control_not_fault {source : TypedSource} {context : SourceSemantics.Context}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : TypedLexicalControl.Syntax source context mode statements expected)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before
      statements finalContext (.fault reason) after) : False := by
  cases syntax_control_shape syntaxTree unique executed

private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ = CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

private theorem finish_from_flow
    {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {source : TypedSource} {context actualContext finalContext : SourceSemantics.Context}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {sourceBefore sourceAfter : Dynamic.Heap}
    {statements : List StatementId} {environment : Environment} {before after : Store}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (syntaxTree : TypedLexicalControl.Syntax source context true statements expected)
    (unique : NodeOccurrencesUnique source)
    (trace : Executes true program actualContext evidence source sourceEnvironment sourceBefore statements finalContext outcome sourceAfter)
    (projection : values.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word)
    (represented : TypedScopedStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough nextEnvironment =>
    have raw := true_fallthrough_unit syntaxTree unique trace
    subst expected
    have native : type = .unit := by
      change Except.ok (.unit : Ty) = .ok type at projection
      exact Except.ok.inj projection.symm
    subst type
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated)
      (by simpa [LanguageResult.success, Expr.weakenAt] using
        (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)),
      .fallthrough nextEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include definitions registered extension contextValid unique uninitialized missing in
theorem Certificate.preserves
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.preserves functions definitions registered extension program function.evidence uninitialized missing
      contextValid unique environments heaps locals agrees actualTyped reference read unmapped sourceTrace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions certificate.syntaxTree unique sourceTrace
    certificate.projection fellThrough escaped represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [certificate.emitted, finish_rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, body_result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩⟩

include definitions registered extension contextValid unique uninitialized missing in
theorem Certificate.reflects
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  rw [certificate.emitted, finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEval⟩ := finish_input evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.reflects functions definitions registered extension program function.evidence uninitialized missing
      contextValid environments heaps locals agrees actualTyped reference read unmapped flowEval
  obtain ⟨result, completed, related⟩ := finish_from_flow functions certificate.syntaxTree unique trace
    certificate.projection fellThrough escaped represented flowEval
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (control_not_fault certificate.syntaxTree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩⟩


end Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody
