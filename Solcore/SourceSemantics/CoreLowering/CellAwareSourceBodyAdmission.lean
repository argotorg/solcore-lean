import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission

/-! A bounded source scanner for lexical generalized declarations followed by
an actual returned expression. Every declared descriptor retains its exact
compiler catalog binding. The ordinary statement scanner is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyAdmission
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

/-- These are decidable observations of one actual catalog at the source site.
The initializer search and binder lookup remain separate compiler actions. -/
structure Site (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (binder : TypedBinder) (initializer : ExpressionId) where
  binding : Binding
  initial : Binding
  located : locals.binding caller binder.id = .ok binding
  selected : locals.bindings.find? (fun entry =>
    decide (entry.caller = caller ∧ entry.initializer = initializer)) = some initial
  selectedBinder : initial.binder.id = binder.id
  bindingCaller : binding.caller = caller
  bindingInitializer : binding.initializer = initializer
  bindingMetadata : binding.binder.applySubstitution active = binder
  bindingSource : binding.source.applySubstitution active = source

def site? (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (binder : TypedBinder) (initializer : ExpressionId) :
    Option (Site locals caller active source binder initializer) :=
  match located : locals.binding caller binder.id with
  | .error _ => none
  | .ok binding =>
    match selected : locals.bindings.find? (fun entry =>
        decide (entry.caller = caller ∧ entry.initializer = initializer)) with
    | none => none
    | some initial =>
      if selectedBinder : initial.binder.id = binder.id then
        if bindingCaller : binding.caller = caller then
          if bindingInitializer : binding.initializer = initializer then
            if bindingMetadata : binding.binder.applySubstitution active = binder then
              if bindingSource : binding.source.applySubstitution active = source then
                some ⟨binding, initial, located, selected, selectedBinder, bindingCaller,
                  bindingInitializer, bindingMetadata, bindingSource⟩
              else none
            else none
          else none
        else none
      else none

inductive Scan (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    Bool → List StatementId → Prop where
  | returning {mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan locals caller active source approved expected mode (id :: rest)
  | tail {id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan locals caller active source approved expected true [id]
  | generalizedInitialized {mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

def scan? (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Scan locals caller active source approved expected mode statements))
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, mode, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      match form : node.form with
      | .returnStmt (some value) =>
        if sourceType : node.type = expected then
          match valueFound : source.lookupExpression? value with
          | none => none
          | some valueNode =>
            if valueType : valueNode.type = expected then do
              let ⟨approved⟩ ← expression value
              pure ⟨.returning rest found form sourceType valueFound valueType approved⟩
            else none
        else none
      | .expression value false =>
        match _modeEq : mode, _restEq : rest with
        | true, [] =>
          if sourceType : node.type = expected then
            match valueFound : source.lookupExpression? value with
            | none => none
            | some valueNode =>
              if valueType : valueNode.type = expected then do
                let ⟨approved⟩ ← expression value
                pure ⟨.tail found form sourceType valueFound valueType approved⟩
              else none
          else none
        | _, _ => none
      | .letDecl binder (some initializer) =>
        if sourceType : node.type = .unit then
          if polymorphic : binder.scheme.quantified ≠ [] then
            if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
              if declaration : (SourceCoreDataPlaces.declaredBinders source).filter
                  (fun actual => decide (actual.id = binder.id)) = [binder] then
                match initializerFound : source.lookupExpression? initializer with
                | none => none
                | some initializerNode =>
                  match initializerForm : initializerNode.form with
                  | .lambda _parameters _result _body =>
                    if valueType : initializerNode.type = binder.scheme.body then
                      if requirements : initializerNode.requirements = [] then
                        if coercions : initializerNode.coercions = [] then do
                          let site ← site? locals caller active source binder initializer
                          let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                          pure ⟨.generalizedInitialized found form sourceType declaration polymorphic ordinary initializerFound
                            initializerForm valueType requirements coercions site remaining⟩
                        else none
                      else none
                    else none
                  | _ => none
              else none
            else none
          else none
        else none
      | _ => none

inductive Syntax (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    SourceSemantics.Context → Bool → List StatementId → Prop where
  | returning {context mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type) (value : approved expression) :
      Syntax locals caller active source approved expected context mode (id :: rest)
  | tail {context id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type) (value : approved expression) :
      Syntax locals caller active source approved expected context true [id]
  | generalizedInitialized {context nextContext mode id node binder initializer initializerNode parameters result body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result body)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = []) (coercions : initializerNode.coercions = [])
      (site : Site locals caller active source binder initializer)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)

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

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

/-- Context extension and child typing come from the original source checker,
including its generalized declaration rule. -/
theorem Scan.syntax {locals caller active source approved expected mode statements}
    (scan : Scan locals caller active source approved expected mode statements)
    (unique : NodeOccurrencesUnique source) {control : ControlContext} (result : control.returnType = expected)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    Syntax locals caller active source approved expected context mode statements := by
  induction scan generalizing control context final facts with
  | returning rest found form _ expressionFound valueType value =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | returnValue actual =>
      exact .returning rest found form expressionFound valueType
        (by simpa only [result, valueType] using actual) value
  | tail found form _ expressionFound valueType value =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | expressionValue actual =>
      exact .tail found form expressionFound valueType (expression_at unique expressionFound actual) value
  | generalizedInitialized found form _ declaration polymorphic ordinary initializerFound initializerForm valueType requirements coercions site _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | letInitialized _ monomorphic _ => exact False.elim (polymorphic monomorphic)
    | letInitializedGeneralized _ _ _ _ extended =>
      exact .generalizedInitialized found form declaration polymorphic extended ordinary initializerFound
        initializerForm valueType requirements coercions site (ih result tail)

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyAdmission
