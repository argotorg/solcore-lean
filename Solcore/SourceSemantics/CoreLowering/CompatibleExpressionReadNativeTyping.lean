import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning

/-! Successful checked reads supply the native type facts needed by the
ordinary cell and lazy mapping branches. Quoted data uses the actual encoder
typing together with checked projection; runtime value typing alone does not
authenticate the annotations on unused sum branches. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference
open CompatibleMapping.VirtualRoot

/-- The checked projection retains native well-formedness under its actual
catalog. A raw projection equation alone does not supply this fact. -/
theorem projectType_wellFormed {checked : SourceCoreCompatibleCatalog.Checked}
    {site : SourceCoreElaboration.ErrorSite} {sourceType : TypeSystem.Ty} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.projectType checked site sourceType = .ok type) :
    type.WellFormed checked.catalog.definitions := by
  unfold SourceCoreCompatibleDataExpressions.projectType at accepted
  cases projected : checked.project sourceType with
  | error error => simp [projected, Except.map, Except.mapError] at accepted
  | ok projection =>
    simp only [projected, Except.map, Except.mapError, Except.ok.injEq] at accepted
    subst type
    exact projection.typed

theorem readExpression_wellFormed {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readExpression checked source id = .ok (node, type)) :
    type.WellFormed checked.catalog.definitions := by
  have metadata := metadata_of_read accepted
  rw [SourceCoreCompatibleDataExpressions.readExpression, if_neg (not_not_intro metadata.owner), metadata.found]
    at accepted
  simp only [metadata.requirements, metadata.coercions, List.isEmpty_nil,
    pure, Except.pure, bind, Except.bind] at accepted
  cases projected : SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) node.type with
  | error error => simp [projected] at accepted
  | ok native =>
    simp only [projected] at accepted
    cases accepted
    exact projectType_wellFormed projected

/-- A quoted value becomes a typed expression in any context. The complete
definition table supplies the types of constructor payloads. -/
theorem quoted_hasType {definitions : DataEnvironment} {world : StoreTyping} {value : Value} {code : Expr} {type : Ty}
    (quoted : Quoted value code) (typed : RuntimeValueHasType world value type definitions)
    (wellFormed : type.WellFormed definitions) (definitionsTyped : definitions.WellFormed)
    (context : Core.Context) : HasType context code type definitions := by
  induction quoted generalizing type with
  | unit => cases typed; exact .unit
  | bool => cases typed; exact .bool
  | word => cases typed; exact .word
  | integer => cases typed; exact .integer
  | pair left right first second =>
    cases typed with
    | pair firstTyped secondTyped =>
      cases wellFormed with
      | product firstWF secondWF => exact .pair (first firstTyped firstWF) (second secondTyped secondWF)
  | inLeft _ quoted ih =>
    cases typed with
    | inLeft typed =>
      cases wellFormed with
      | sum leftWF rightWF => exact .inLeft rightWF (ih typed leftWF)
  | inRight _ quoted ih =>
    cases typed with
    | inRight typed =>
      cases wellFormed with
      | sum leftWF rightWF => exact .inRight leftWF (ih typed rightWF)
  | constructed _ quoted ih =>
    cases typed with
    | constructed found typed =>
      exact .construct found (ih typed (definitionsTyped.constructorPayloadType_wellFormed found))

theorem Literal.native_hasType {fuel : Nat} {values : ValuesContext} {node : ExpressionNode}
    {sourceType : TypeSystem.Ty} {carrier : SourceCoreCompatibleValues.Value} {code : Expr} {type : Ty}
    (literal : Literal fuel values node sourceType carrier code)
    (projection : values.checked.catalog.project sourceType = .ok type)
    (wellFormed : type.WellFormed values.checked.catalog.definitions)
    (context : Core.Context) : HasType context code type values.checked.catalog.definitions := by
  cases literal with
  | encoded encoded _ _ quoted =>
    have same : encoded.type = type := Except.ok.inj (encoded.projected.symm.trans projection)
    exact quoted_hasType (quoted_of_quote quoted) (same ▸ encoded.typed []) wellFormed
      values.checked.definitionsTyped context

theorem ReadCode.native_hasType {fuel : Nat} {values : ValuesContext} {node : ExpressionNode}
    {declared : TypedBinder} {index : Nat} {type : Ty} {reason : Word} {code : Expr} {context : Core.Context}
    (emitted : ReadCode fuel values node declared index type reason code)
    (projection : values.checked.catalog.project declared.scheme.body = .ok type)
    (wellFormed : type.WellFormed values.checked.catalog.definitions)
    (reference : HasType context (.var index) (OptionalCell.referenceType type) values.checked.catalog.definitions) :
    HasType context code (LanguageResult.resultType type) values.checked.catalog.definitions := by
  cases emitted with
  | ordinary => exact OptionalCell.read_hasType reason wellFormed reference
  | mapping _ literal =>
    exact SourceCoreCompatibleDataExpressions.readMapping_hasType reference
      (literal.native_hasType projection wellFormed _)

/-- The static source declaration fixes the raw type of the lazily produced
empty mapping. Both branches use the actual compiler scope and checked type. -/
theorem Certificate.native_hasType {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    {sourceContext : SourceSemantics.Context} (binding : StaticBinding certificate sourceContext)
    (wellFormed : certificate.type.WellFormed values.checked.catalog.definitions)
    (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code
      (LanguageResult.resultType certificate.type) values.checked.catalog.definitions := by
  have selected := SourceCoreLocalCell.lookup?_context certificate.slot
  have reference : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) (.var certificate.index)
      (OptionalCell.referenceType certificate.type) values.checked.catalog.definitions :=
    .var ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp selected).1).trans selected)
  have projection : values.checked.catalog.project certificate.declared.scheme.body = .ok certificate.type := by
    rw [← values.checked.catalog.project_runtimeType certificate.declared.scheme.body,
      ← binding.occurrence, values.checked.catalog.project_runtimeType certificate.node.type]
    exact certificate.metadata.projected
  exact certificate.emitted.native_hasType projection wellFormed reference

/-- Actual accepted lowering and the independent source typing judgment close
native read typing. There is no child execution or native typing premise. -/
theorem loweredRead_native_hasType {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source) (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) values.checked.catalog.definitions := by
  obtain ⟨certificate, same, binding⟩ := loweredRead_of_accepted accepted read unique declarations typed
  have wellFormed := readExpression_wellFormed read
  rw [← same] at wellFormed
  simpa only [same] using certificate.native_hasType binding wellFormed administrative

/-- Generated frame and helper definitions can be appended without changing
the accepted read's code, local reference positions or native result type. -/
theorem loweredRead_native_hasType_at {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source) (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) (administrative : Core.Context)
    {definitions : DataEnvironment} (extension : values.checked.catalog.definitions.Extends definitions) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) definitions :=
  (loweredRead_native_hasType accepted read unique declarations typed administrative).extend_definitions extension

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
