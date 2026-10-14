import Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
import Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyStopping

/-! Finite original statement admission separates syntax from lexical typing.
The same scan yields the accepted body shape and recovers changing contexts
from independent Source statement typing, including loop control contexts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
open Core Frontend SourceInference

inductive Scan (source : TypedSource) (approved : ExpressionId → Prop)
    (expected : TypeSystem.Ty) : Bool → List StatementId → Prop where
  | nil {mode} (allowed : mode = false ∨ expected = .unit) : Scan source approved expected mode []
  | breaking {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) : Scan source approved expected mode (id :: rest)
  | continuing {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) : Scan source approved expected mode (id :: rest)
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) (result : expected = .unit) :
      Scan source approved expected mode (id :: rest)
  | returning {mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan source approved expected mode (id :: rest)
  | tail {id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan source approved expected true [id]
  | absent {mode id node binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | initialized {mode id node binder expression expressionNode rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = binder.scheme.body) (value : approved expression)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | discard {mode id node expression expressionNode semicolon rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (continuing : semicolon = true ∨ mode = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : approved expression) (remaining : Scan source approved expected mode rest) :
      Scan source approved expected mode (id :: rest)
  | block {mode id node body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block body)
      (inner : Scan source approved expected false body)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | conditional {mode id node condition conditionNode thenBody elseBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit ∨ node.type = expected)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (left : Scan source approved expected false thenBody)
      (right : Scan source approved expected false (elseBody.getD []))
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | whileLoop {mode id node condition conditionNode body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition body)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (inner : Scan source approved expected false body)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | matching {mode id node resolution scrutineeNode rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (value : approved resolution.scrutinee)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (arms : ∀ arm ∈ resolution.cases, Scan source approved expected false arm.body)
      (fallback : ∀ statements, resolution.defaultBody = some statements → Scan source approved expected false statements)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | forLoop {mode id node initializer condition conditionNode post body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post body)
      (sourceType : node.type = .unit)
      (initial : ScopedSourceForItemsAdmission.Scan source approved initializer)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (inner : Scan source approved expected false body)
      (after : ScopedSourceForItemsAdmission.Scan source approved post)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | assign {mode id node assignment operator rhs rhsNode binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)

  | terminalBlock {mode id node body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block body)
      (sourceType : node.type = expected)
      (inner : Scan source approved expected false body)
      (stops : ScopedSourceBodyStopping.ReturnStopped source body)
      (remaining : CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode rest) :
      Scan source approved expected mode (id :: rest)
  | terminalConditional {mode id node condition conditionNode leftBody rightBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition leftBody (some rightBody))
      (sourceType : node.type = expected)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (left : Scan source approved expected false leftBody)
      (right : Scan source approved expected false rightBody)
      (first : ScopedSourceBodyStopping.ReturnStopped source leftBody)
      (second : ScopedSourceBodyStopping.ReturnStopped source rightBody)
      (remaining : CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode rest) :
      Scan source approved expected mode (id :: rest)
  | terminalMatch {mode id node resolution scrutineeNode defaultBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (sourceType : node.type = expected)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (value : approved resolution.scrutinee)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (arms : ∀ arm ∈ resolution.cases, Scan source approved expected false arm.body)
      (fallback : ∀ statements, resolution.defaultBody = some statements → Scan source approved expected false statements)
      (present : resolution.defaultBody = some defaultBody)
      (stoppedArms : ∀ arm ∈ resolution.cases, ScopedSourceBodyStopping.ReturnStopped source arm.body)
      (stoppedDefault : ScopedSourceBodyStopping.ReturnStopped source defaultBody)
      (remaining : CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode rest) :
      Scan source approved expected mode (id :: rest)

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

theorem Scan.shape {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode statements := by
  induction scan with
  | nil => exact .nil
  | breaking rest found form => exact .breaking rest found form
  | continuing rest found form => exact .continuing rest found form
  | returnUnit rest found form => exact .returnUnit rest found form
  | returning rest found form => exact .returnValue rest found form
  | tail found form => exact .tail found form
  | absent found form _ _ _ _ ih => exact .absent found form ih
  | initialized found form _ _ _ _ _ _ _ ih => exact .initialized found form ih
  | discard found form continuing _ _ _ _ ih => exact .discard found form continuing ih
  | block found form _ _ inner remaining => exact .block found form inner remaining
  | conditional found form _ _ _ _ _ _ _ left right remaining => exact .conditional found form left right remaining
  | whileLoop found form _ _ _ _ _ inner remaining => exact .whileLoop found form inner remaining
  | assign found form _ _ profile bare _ _ _ _ ih => exact .assign found form profile bare ih
  | matching found form _ _ _ _ _ _ _ arms fallback remaining =>
      exact .matchWith found form arms fallback remaining
  | forLoop found form _ initial _ _ _ _ after _ inner remaining =>
      exact .forLoop found form initial.shape after.shape inner remaining
  | terminalBlock found form _ _ _ remaining inner => exact .block found form inner remaining
  | terminalConditional found form _ _ _ _ _ _ _ _ remaining left right =>
      exact .conditional found form left right remaining
  | terminalMatch found form _ _ _ _ _ _ _ _ _ _ remaining arms fallback =>
      exact .matchWith found form arms fallback remaining

/-- Changing loop depth is harmless because each recursive body retains the
same actual return type. All writes come from the original assignment typing. -/
theorem Scan.syntax {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) (unique : NodeOccurrencesUnique source)
    {control : ControlContext} (result : control.returnType = expected)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode statements) expected := by
  induction scan generalizing control context final facts with
  | nil allowed => exact .body (.nil allowed)
  | breaking rest found form => exact .breaking found form
  | continuing rest found form => exact .continuing found form
  | returnUnit rest found form sourceType expectedUnit =>
      subst expected
      exact .body (.returnUnit rest found form sourceType)
  | returning rest found form sourceType expressionFound valueType value =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnValue actual =>
        exact .body (.returnValue rest found form sourceType expressionFound valueType
          (by simpa only [result, valueType] using actual) value)
  | tail found form sourceType expressionFound valueType value =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | expressionValue actual =>
        exact .body (.tail found form sourceType expressionFound valueType (expression_at unique expressionFound actual) value)
  | absent found form declaration monomorphic ordinary _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letUninitialized _ extended => exact .uninitialized found form declaration monomorphic extended ordinary (ih result tail)
  | initialized found form declaration monomorphic ordinary expressionFound valueType value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letInitialized actual _ extended =>
        exact .initialized found form declaration monomorphic extended ordinary expressionFound valueType
          (by simpa only [valueType] using actual) value (ih result tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)
  | discard found form continuing sourceType expressionFound value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | expressionValue actual | expressionDiscard actual =>
        exact .discard found form (by rcases continuing with same | same <;> simp_all) sourceType expressionFound (expression_at unique expressionFound actual) value (ih result tail)
  | block found form _ _ inner remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block actual => exact .scopedBlock found form (inner result actual) (remaining result tail)
  | conditional found form sourceType conditionFound conditionType value _ _ _ left right remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithoutElse condition actual =>
        exact .ifThen found form sourceType conditionFound conditionType
          (by simpa only [conditionType] using condition) value (left result actual)
          (right result (.nil _ _)) (remaining result tail)
      | ifWithElse condition first second =>
        exact .ifThen found form sourceType conditionFound conditionType
          (by simpa only [conditionType] using condition) value (left result first)
          (right result second) (remaining result tail)
  | whileLoop found form conditionFound conditionType value _ _ inner remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | whileLoop condition actual =>
        exact .whileLoop found form conditionFound conditionType
          (by simpa only [conditionType] using condition) value (inner (control := control.enterLoop) result actual) (remaining result tail)
  | assign found form declaration targetType profile bare rhsFound rhsType value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignValue assignment =>
        obtain ⟨sourceTyped, writable, rightTyped, numeric⟩ :=
          ScopedSourceForItemsAdmission.assignment_facts declaration targetType bare assignment
        apply GenericImperativeMatch.Syntax.assign found form sourceTyped writable rightTyped numeric
        · intro child member
          simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
          subst child
          exact ⟨value, _, rhsFound, expression_at unique rhsFound rightTyped⟩
        · exact ih result tail

  | matching found form scrutineeFound value hiddenOrdinary armsOrdinary _ _ _ arms fallback remaining =>
      obtain ⟨middle, headFacts, tailFacts, head, tail⟩ := head_tail typed
      obtain ⟨sameContext, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
        ScopedSourceMatchAdmission.statement_sites unique found form scrutineeFound head
      subst middle
      have sourceType := ScopedSourceMatchAdmission.statement_type unique found form head
      rw [result] at sourceType
      apply GenericImperativeMatch.Syntax.matchWith found form sourceType scrutineeFound scrutineeTyped
        value casesTyped defaultTyped hiddenOrdinary armsOrdinary
      · intro request childContext selected
        obtain ⟨last, childFacts, childTyped⟩ :=
          ScopedSourceMatchAdmission.request_typing casesTyped defaultTyped selected
        cases selected with
        | arm member same _ _ =>
          rw [same] at childTyped ⊢
          exact arms _ member result childTyped
        | default same => exact fallback _ same result childTyped
      · exact remaining result tail

  | forLoop found form sourceType initial conditionFound conditionType value _ after _ inner remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | forLoop initTyped condition body postTyped =>
        exact .forLoop found form sourceType
          (ScopedSourceForItemsAdmission.initializers (initial.syntax unique initTyped) initTyped
            (.initializersDone conditionFound conditionType (expression_at unique conditionFound condition) value
              (inner (control := control.enterLoop) result body) (after.syntax unique postTyped)))
          (remaining result tail)


  | terminalBlock found form sourceType _ stops _ inner =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block body =>
          exact .terminalBlock unique found form sourceType
            (inner result body) (stops.stopped unique body)
  | terminalConditional found form sourceType conditionFound conditionType value _ _ first second _ left right =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithElse condition firstTyped secondTyped =>
          exact .terminalIf unique found form sourceType conditionFound conditionType
            (by simpa only [conditionType] using condition) value
            (left result firstTyped) (right result secondTyped)
            (first.stopped unique firstTyped) (second.stopped unique secondTyped)
  | terminalMatch found form sourceType scrutineeFound value hiddenOrdinary armsOrdinary _ _ present stoppedArms stoppedDefault _ arms fallback =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      obtain ⟨_, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
        ScopedSourceMatchAdmission.statement_sites unique found form scrutineeFound head
      apply GenericImperativeMatch.Syntax.terminalMatch unique found form (.inr sourceType)
        scrutineeFound scrutineeTyped value casesTyped defaultTyped hiddenOrdinary armsOrdinary
      · intro request childContext selected
        obtain ⟨last, childFacts, childTyped⟩ :=
          ScopedSourceMatchAdmission.request_typing casesTyped defaultTyped selected
        cases selected with
        | arm member same _ _ =>
          rw [same] at childTyped ⊢
          exact arms _ member result childTyped
        | default same => exact fallback _ same result childTyped
      · exact ScopedSourceBodyStopping.ReturnStopped.match_default stoppedArms stoppedDefault
          unique found form present head

/-- The expression checker is a data-only parameter; the finite traversal uses
its proof receipts without evaluating any selected semantic inventory. -/
def scan? (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Scan source approved expected mode statements))
  | 0, _, _ => none
  | fuel + 1, mode, [] =>
      if allowed : mode = false ∨ expected = .unit then some ⟨.nil allowed⟩ else none
  | fuel + 1, mode, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      match form : node.form with
      | .returnStmt none =>
        if result : expected = .unit then
          if sourceType : node.type = .unit then some ⟨.returnUnit rest found form sourceType result⟩ else none
        else none
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
      | .expression value semicolon =>
        match valueFound : source.lookupExpression? value with
        | none => none
        | some valueNode =>
          if continuing : semicolon = true ∨ mode = false then
            if sourceType : node.type = if semicolon then .unit else valueNode.type then do
              let ⟨approved⟩ ← expression value
              let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
              pure ⟨.discard found form continuing sourceType valueFound approved remaining⟩
            else none
          else
            match semicolonEq : semicolon, modeEq : mode, restEq : rest with
            | false, true, [] =>
              if sourceType : node.type = expected then
                if valueType : valueNode.type = expected then do
                  let ⟨approved⟩ ← expression value
                  pure ⟨.tail found (by simpa only [semicolonEq] using form) sourceType valueFound valueType approved⟩
                else none
              else none
            | _, _, _ => none
      | .letDecl binder initializer =>
        if monomorphic : binder.scheme.quantified = [] then
          if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
            match declaration : SourceCoreDataPlaces.rootBinder source binder.id with
            | .error _ => none
            | .ok actual =>
              if same : actual = binder then
                match initializer with
                | none => do
                  let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
                  pure ⟨.absent found form (by simpa only [same] using declaration) monomorphic ordinary remaining⟩
                | some value =>
                  match valueFound : source.lookupExpression? value with
                  | none => none
                  | some valueNode =>
                    if valueType : valueNode.type = binder.scheme.body then do
                      let ⟨approved⟩ ← expression value
                      let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
                      pure ⟨.initialized found form (by simpa only [same] using declaration)
                        monomorphic ordinary valueFound valueType approved remaining⟩
                    else none
              else none
          else none
        else none
      | .block body => do
        let ⟨inner⟩ ← scan? source expression expected fuel false body
        let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
        pure ⟨.block found form inner remaining⟩
      | .ifThen condition thenBody elseBody =>
        if sourceType : node.type = .unit ∨ node.type = expected then
          match conditionFound : source.lookupExpression? condition with
          | none => none
          | some conditionNode =>
            if conditionType : conditionNode.type = .bool then do
              let ⟨approved⟩ ← expression condition
              let ⟨left⟩ ← scan? source expression expected fuel false thenBody
              let ⟨right⟩ ← scan? source expression expected fuel false (elseBody.getD [])
              let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
              pure ⟨.conditional found form sourceType conditionFound conditionType approved left right remaining⟩
            else none
        else none
      | .whileLoop condition body =>
        match conditionFound : source.lookupExpression? condition with
        | none => none
        | some conditionNode =>
          if conditionType : conditionNode.type = .bool then do
            let ⟨approved⟩ ← expression condition
            let ⟨inner⟩ ← scan? source expression expected fuel false body
            let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
            pure ⟨.whileLoop found form conditionFound conditionType approved inner remaining⟩
          else none
      | .assignValue assignment operator rhs =>
        if profile : operator = .equal ∨ assignment.target.type = .word then
          if bare : assignment.target.projections = [] then
            match declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root with
            | .error _ => none
            | .ok binder =>
              if targetType : binder.scheme.body = assignment.target.type then
                match rhsFound : source.lookupExpression? rhs with
                | none => none
                | some rhsNode =>
                  if rhsType : rhsNode.type = assignment.target.type then do
                    let ⟨approved⟩ ← expression rhs
                    let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
                    pure ⟨.assign found form declaration targetType profile bare rhsFound rhsType approved remaining⟩
                  else none
              else none
          else none
        else none
      | _ => none

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
