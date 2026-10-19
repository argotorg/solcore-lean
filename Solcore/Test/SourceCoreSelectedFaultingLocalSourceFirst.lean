import Solcore.Test.SourceCoreSelectedFaultingLocalTrace

/-! Original checker typing supplies both materialized closure frames before
the independent Source execution. No completed native call is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Frontend SourceInference SourceSemantics

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem Shape.literal_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.wordCall.node.id type) :
    ∃ literalType, ExpressionHasType source context shape.literal.node.id literalType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.wordCall.found)
    rw [shape.wordCall.form] at raw
    cases raw with
    | indirectCall _ arguments _ =>
      cases arguments with
      | cons literal _ => exact ⟨_, literal⟩

/-- Original declaration typing supplies the actual Word instance frame and
both ordinary binder extensions before the independent fault trace is built. -/
theorem Shape.body_from_source {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {control : ControlContext} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (typed : StatementsHaveType source control context
      [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id] final facts) :
    ∃ nextContext, Dynamic.FunctionStatementsFault program context evidence source environment before
      [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id] nextContext
      (shape.failure context environment before) (shape.finalHeap context environment before) := by
  have unique := runtime.graph.nodeOccurrencesUnique
  obtain ⟨next, _, _, first, rest⟩ := head_tail typed
  have original := form_at unique shape.initializedFound first
  rw [shape.initializedForm] at original
  cases original with
  | letInitialized _ monomorphic _ =>
    rw [shape.scheme] at monomorphic
    cases monomorphic
  | letInitializedGeneralized polymorphic requirements generalizes initializer extended =>
    have descriptorTyped := (shape.captures context environment).wellTyped runtime locals
      polymorphic requirements generalizes initializer extended
    have fields := Dynamic.RuntimeContextFields.ofBinderExtends extended
    obtain ⟨valueContext, _, _, valueStatement, absentRest⟩ := head_tail rest
    have originalValue := form_at unique shape.valueFound valueStatement
    rw [shape.valueForm] at originalValue
    cases originalValue with
    | letInitializedGeneralized impossible _ _ _ _ =>
      exact False.elim (impossible (by rw [shape.valueScheme]; rfl))
    | letInitialized valueTyped _ valueExtended =>
      obtain ⟨literalType, literal⟩ := shape.literal_typed unique valueTyped
      obtain ⟨absentContext, _, _, absentStatement, _remaining⟩ := head_tail absentRest
      have originalAbsent := form_at unique shape.absentFound absentStatement
      rw [shape.absentForm] at originalAbsent
      cases originalAbsent with
      | letUninitialized _ absentExtended =>
        cases extended with
        | intro wellformed fresh =>
          have scheme : SchemeWellFormed
              (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
              shape.binder.scheme := {
            binders := wellformed.scheme.binders.withLocal _ _ _
            quantified_nodup := wellformed.scheme.quantified_nodup
            body := wellformed.scheme.body.withLocal _ _ _
          }
          have word : TypeWellFormed
              (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) .word :=
            ⟨scheme.binders, .builtin .word⟩
          have descriptorNext : Dynamic.GeneralizedClosureWellTyped
              (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
              before (shape.descriptor context environment) :=
            ⟨descriptorTyped.same_signatures, descriptorTyped.code, descriptorTyped.captures⟩
          exact ⟨_, shape.body_trace evidence environment before unique (.intro wellformed fresh)
            valueExtended absentExtended fields scheme word literal
            (shape.frame environment before evidence catalog descriptorNext fields runtime.signatures
              (fields.covers covers) scheme word)⟩

end Tests.SourceCoreSelectedFaultingLocal
