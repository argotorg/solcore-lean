import Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission

/-! The finite header profile retains original declarations and bare writable
places. Actual Source typing determines every context along the header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderAdmission
open Core Frontend SourceInference

inductive Scan (source : TypedSource) (approved : ExpressionId → Prop) : List ForItemForm → Prop where
  | nil : Scan source approved []
  | absent {binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder none :: rest)
  | initialized {binder expression expressionNode rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = binder.scheme.body) (value : approved expression)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder (some expression) :: rest)
  | discard {expression expressionNode rest}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : approved expression) (remaining : Scan source approved rest) :
      Scan source approved (.expression expression :: rest)
  | assign {assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved rest) : Scan source approved (.assignValue assignment operator rhs :: rest)

  | assignProjected {assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type)
      (value : approved rhs)
      (remaining : Scan source approved rest) : Scan source approved (.assignValue assignment operator rhs :: rest)


def approvedKeys? {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) :
    (ids : List ExpressionId) → Option (PLift (∀ id ∈ ids, approved id))
  | [] => some ⟨by intro id member; cases member⟩
  | id :: ids => do
    let ⟨head⟩ ← expression id
    let ⟨tail⟩ ← approvedKeys? expression ids
    pure ⟨by intro child member; rcases List.mem_cons.mp member with same | rest
             · exact same ▸ head
             · exact tail child rest⟩

def scan? (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) :
    (items : List ForItemForm) → Option (PLift (Scan source approved items))
  | [] => some ⟨.nil⟩
  | .letDecl binder initializer :: rest =>
    match declaration : SourceCoreDataPlaces.rootBinder source binder.id with
    | .error _ => none
    | .ok actual =>
      if same : actual = binder then
        have declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := same ▸ declaration
        if mono : binder.scheme.quantified = [] then
          if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
            match initializer with
            | none => do
              let ⟨remaining⟩ ← scan? source expression rest
              pure ⟨.absent declaration mono ordinary remaining⟩
            | some value =>
              match found : source.lookupExpression? value with
              | none => none
              | some node =>
                if valueType : node.type = binder.scheme.body then do
                  let ⟨approved⟩ ← expression value
                  let ⟨remaining⟩ ← scan? source expression rest
                  pure ⟨.initialized declaration mono ordinary found valueType approved remaining⟩
                else none
          else none
        else none
      else none
  | .expression value :: rest =>
    match found : source.lookupExpression? value with
    | none => none
    | some _ => do
      let ⟨approved⟩ ← expression value
      let ⟨remaining⟩ ← scan? source expression rest
      pure ⟨.discard found approved remaining⟩
  | .assignValue assignment operator rhs :: rest =>
    match declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root with
    | .error _ => none
    | .ok binder =>
      if profile : operator = .equal ∨ assignment.target.type = .word then
        match rhsFound : source.lookupExpression? rhs with
        | none => none
        | some rhsNode =>
          if rhsType : rhsNode.type = assignment.target.type then do
            let ⟨value⟩ ← expression rhs
            let ⟨remaining⟩ ← scan? source expression rest
            if bare : assignment.target.projections = [] then
              if targetType : binder.scheme.body = assignment.target.type then
                pure ⟨.assign declaration targetType profile bare rhsFound rhsType value remaining⟩
              else none
            else
              let ⟨route⟩ ← AcceptedProjectedAssignmentRoute.check source binder.scheme.body assignment.target.projections assignment.target.type
              let ⟨keys⟩ ← CellAwareForHeaderAdmission.approvedKeys? expression (DataPlaceKeyOrder.sourceKeys assignment.target.projections)
              pure ⟨.assignProjected declaration route profile bare keys rhsFound rhsType value remaining⟩
          else none
      else none
  | .assignBitNot _ :: _ => none

inductive Syntax (source : TypedSource) (approved : ExpressionId → Prop) :
    SourceSemantics.Context → List ForItemForm → SourceSemantics.Context → Prop where
  | nil {context} : Syntax source approved context [] context
  | absent {context nextContext final binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source approved nextContext rest final) :
      Syntax source approved context (.letDecl binder none :: rest) final
  | initialized {context nextContext final binder initializer node rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : source.lookupExpression? initializer = some node)
      (sourceType : node.type = binder.scheme.body)
      (typed : ExpressionHasType source context initializer node.type)
      (value : approved initializer)
      (remaining : Syntax source approved nextContext rest final) :
      Syntax source approved context (.letDecl binder (some initializer) :: rest) final
  | discard {context final expression node rest}
      (found : source.lookupExpression? expression = some node)
      (typed : ExpressionHasType source context expression node.type)
      (value : approved expression)
      (remaining : Syntax source approved context rest final) :
      Syntax source approved context (.expression expression :: rest) final
  | assign {context final assignment operator rhs node binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (found : source.lookupExpression? rhs = some node)
      (sourceType : node.type = assignment.target.type)
      (typed : SourceAssignmentHasType source context assignment operator rhs)
      (value : approved rhs)
      (remaining : Syntax source approved context rest final) :
      Syntax source approved context (.assignValue assignment operator rhs :: rest) final

  | assignProjected {context final assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type)
      (typed : SourceAssignmentHasType source context assignment operator rhs)
      (value : approved rhs)
      (remaining : Syntax source approved context rest final) :
      Syntax source approved context (.assignValue assignment operator rhs :: rest) final


private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

theorem Scan.syntax {source approved items} (scan : Scan source approved items)
    {context final : SourceSemantics.Context} {control : ControlContext}
    (unique : NodeOccurrencesUnique source) (typed : ForItemsHaveType source control context items final) :
    Syntax source approved context items final := by
  induction scan generalizing context final with
  | nil => cases typed; exact .nil
  | absent declaration mono ordinary remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | letUninitialized _ _ extended => exact .absent declaration mono extended ordinary (ih tail)
  | initialized declaration mono ordinary found sourceType value remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | letInitialized actual _ _ extended =>
        exact .initialized declaration mono extended ordinary found sourceType (expression_at unique found actual) value (ih tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | discard found value remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | expression actual => exact .discard found (expression_at unique found actual) value (ih tail)
  | assign declaration targetType profile bare found sourceType value remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | assignValue actual => exact .assign declaration targetType profile bare found sourceType actual value (ih tail)

  | assignProjected declaration route profile projected keys rhsFound rhsType value _ ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | assignValue actual =>
        exact .assignProjected declaration route profile projected keys rhsFound rhsType actual value (ih tail)

theorem Syntax.signatures {source approved context items final}
    (tree : Syntax source approved context items final) : final.signatures = context.signatures := by
  induction tree with
  | nil => rfl
  | absent _ _ extended _ _ ih | initialized _ _ extended _ _ _ _ _ _ ih =>
    cases extended
    exact ih
  | discard _ _ _ _ ih | assign _ _ _ _ _ _ _ _ _ ih | assignProjected _ _ _ _ _ _ _ _ _ _ ih => exact ih

end Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderAdmission
