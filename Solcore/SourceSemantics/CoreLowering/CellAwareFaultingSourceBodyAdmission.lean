import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalSourceBodyAdmission

/-! The additive source profile admits ordinary absent declarations
between initialized and generalized declarations. Existing suffixes retain their original
profile, and every new initializer uses the same finite expression profile. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareFaultingSourceBodyAdmission
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open CellAwareSourceBodyAdmission (Site site?)

inductive Scan (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    Bool → List StatementId → Prop where
  | existing {mode statements}
      (scan : CellAwareLexicalSourceBodyAdmission.Scan locals caller active source approved expected mode statements) :
      Scan locals caller active source approved expected mode statements
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
  | initialized {mode id node binder initializer initializerNode rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (mono : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (value : approved initializer)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

  | uninitialized {mode id node binder rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder none)
      (sourceType : node.type = .unit)
      (declaration : (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (mono : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan locals caller active source approved expected mode rest) :
      Scan locals caller active source approved expected mode (id :: rest)

def scan? (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Scan locals caller active source approved expected mode statements))
  | 0, _, _ => none
  | fuel + 1, mode, statements =>
    match CellAwareLexicalSourceBodyAdmission.scan? locals caller active source expression expected (fuel + 1) mode statements with
    | some original => some ⟨.existing original.down⟩
    | none =>
      match statements with
      | [] => none
      | id :: rest =>
        match found : source.lookupStatement? id with
        | none => none
        | some node =>
          match form : node.form with
          | .letDecl binder (some initializer) =>
            if sourceType : node.type = .unit then
              if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
                if declaration : (SourceCoreDataPlaces.declaredBinders source).filter
                    (fun actual => decide (actual.id = binder.id)) = [binder] then
                  match initializerFound : source.lookupExpression? initializer with
                  | none => none
                  | some initializerNode =>
                    if valueType : initializerNode.type = binder.scheme.body then
                      if mono : binder.scheme.quantified = [] then do
                        let ⟨value⟩ ← expression initializer
                        let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                        pure ⟨.initialized found form sourceType declaration mono ordinary initializerFound valueType value remaining⟩
                      else
                        match initializerForm : initializerNode.form with
                        | .lambda _parameters _result _body =>
                          if requirements : initializerNode.requirements = [] then
                            if coercions : initializerNode.coercions = [] then do
                              let site ← site? locals caller active source binder initializer
                              let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                              pure ⟨.generalizedInitialized found form sourceType declaration mono ordinary initializerFound
                                initializerForm valueType requirements coercions site remaining⟩
                            else none
                          else none
                        | _ => none
                    else none
                else none
              else none
            else none
          | .letDecl binder none =>
            if sourceType : node.type = .unit then
              if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
                if declaration : (SourceCoreDataPlaces.declaredBinders source).filter
                    (fun actual => decide (actual.id = binder.id)) = [binder] then
                  if mono : binder.scheme.quantified = [] then do
                    let ⟨remaining⟩ ← scan? locals caller active source expression expected fuel mode rest
                    pure ⟨.uninitialized found form sourceType declaration mono ordinary remaining⟩
                  else none
                else none
              else none
            else none
          | _ => none

inductive Syntax (locals : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) :
    SourceSemantics.Context → Bool → List StatementId → Prop where
  | existing {context mode statements}
      (tree : CellAwareLexicalSourceBodyAdmission.Syntax locals caller active source approved expected context mode statements) :
      Syntax locals caller active source approved expected context mode statements
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
  | initialized {context nextContext mode id node binder initializer initializerNode rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (valueType : initializerNode.type = binder.scheme.body)
      (typed : ExpressionHasType source context initializer initializerNode.type)
      (value : approved initializer)
      (remaining : Syntax locals caller active source approved expected nextContext mode rest) :
      Syntax locals caller active source approved expected context mode (id :: rest)

  | uninitialized {context nextContext mode id node binder rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder none)
      (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
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
  | existing original => exact .existing (original.syntax unique result typed)
  | generalizedInitialized found form _ declaration polymorphic ordinary initializerFound initializerForm valueType requirements coercions site _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | letInitialized _ monomorphic _ => exact False.elim (polymorphic monomorphic)
    | letInitializedGeneralized _ _ _ _ extended =>
      exact .generalizedInitialized found form declaration polymorphic extended ordinary initializerFound
        initializerForm valueType requirements coercions site (ih result tail)
  | initialized found form _ declaration mono ordinary initializerFound valueType value _ ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    have member : _ ∈ SourceCoreDataPlaces.declaredBinders source :=
      (List.mem_filter.mp (declaration ▸ List.mem_singleton_self _)).1
    cases original with
    | letInitialized initial _ extended =>
      exact .initialized found form member mono extended ordinary initializerFound valueType
        (expression_at unique initializerFound initial) value (ih result tail)
    | letInitializedGeneralized quantified _ _ _ _ => exact False.elim (quantified mono)

  | uninitialized found form _ declaration mono ordinary remaining ih =>
    obtain ⟨_, _, _, head, tail⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    have member : _ ∈ SourceCoreDataPlaces.declaredBinders source :=
      (List.mem_filter.mp (declaration ▸ List.mem_singleton_self _)).1
    cases original with
    | letUninitialized _ extended =>
      exact .uninitialized found form member mono extended ordinary (ih result tail)

end Solcore.SourceSemantics.CoreLowering.CellAwareFaultingSourceBodyAdmission
