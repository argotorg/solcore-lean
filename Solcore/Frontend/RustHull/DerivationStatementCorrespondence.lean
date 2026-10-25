import Solcore.Frontend.RustHull.ContextualStatementCorrespondence
import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport
import Solcore.Frontend.RustHull.AssignmentValidity

/-! Statement steps consume simulation hypotheses for the particular source
subderivations. They do not assume a rank on calls or a universal expression
preservation theorem. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationStatementCorrespondence
open Correspondence StatementCorrespondence DerivationCorrespondence

variable {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature}
  {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
  {sourceEnvironment : Semantics.Environment}

/-- The actual compiler checks a local or nested product path. The root is
read after the RHS finishes, and only the selected component is replaced. -/
theorem assign {statement : Stmt} {lhs rhs : Expr}
    {initial middle final : Semantics.State σ} {sourceValue : Semantics.Value}
    (kind : statement.kind = .assign lhs rhs)
    (right : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rhs initial (.value sourceValue) middle)
    (assigned : Semantics.assignResult sourceEnvironment middle lhs sourceValue = .value final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial .fallthrough final := by
  intro fuel scope result loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, name, path, binding, index, updated, rightCompiled, placed,
          looked, _, selected, updatedCompiled, rfl⟩ := assignment_components compiled
      obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        right.value rfl rightCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      obtain ⟨sourceLocation, sourceOld, sourceUpdated, found, read, updateSource, rfl⟩ :=
        assignment_source placed assigned
      obtain ⟨location, entry, _, targetFound⟩ :=
        (environmentRelated.extendWorld extension) name sourceLocation binding index found looked
      obtain ⟨oldValue, targetRead, oldRelated⟩ := middleHeap.read entry read
      have updatedRenamed : updateProduct path binding.type (.var 0) (.var 1) =
          .ok (updated.rename (Core.Renaming.lift (Core.Renaming.lift mapping))) :=
        updateProduct_rename updatedCompiled (Core.Renaming.lift (Core.Renaming.lift mapping))
      have oldEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
          (.var 0) oldValue middleStore := .var rfl
      have valueEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
          (.var 1) value middleStore := .var rfl
      obtain ⟨newValue, newRelated, updatedEvaluated⟩ :=
        updateProduct_evaluates updatedRenamed selected oldRelated valueRelated updateSource oldEvaluated valueEvaluated
      have written : middleStore.write? location (.inRight .unit newValue) =
          some (middleStore.set location (.inRight .unit newValue)) :=
        Core.Store.write?_eq_some_iff.mpr ⟨middleHeap.location_bound entry, rfl⟩
      exact ⟨extension, _, _, .fallthrough, assignment_core evaluated targetFound targetRead updatedEvaluated written,
        middleHeap.write entry newRelated written, middleInstalled.write middleHeap.toHeapRel entry written,
        firstFrame.trans (ClosuresPreserved.write middleHeap.toHeapRel entry written)⟩

theorem returned {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value} (kind : statement.kind = .returnStmt value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.value sourceValue) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.returned sourceValue) final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      have components := compiled
      simp only [lowerStatement] at components
      obtain ⟨lowered, valueCompiled, components⟩ := lower_bind_eq_ok.mp components
      obtain ⟨checked, matched, _⟩ := lower_bind_eq_ok.mp components
      cases checked
      have sameType := expectType_eq_of_ok matched
      obtain ⟨extension, targetValue, finalStore, valueRelated, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        preserves.value rfl valueCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      exact ⟨extension, Core.LocalLoop.returnedValue targetValue, finalStore,
        .returned (sameType ▸ valueRelated), return_success compiled valueCompiled evaluated,
        finalHeap, finalInstalled, lastFrame⟩

theorem expression_statement {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value} (kind : statement.kind = .expression value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.value sourceValue) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial .fallthrough final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨extension, targetValue, finalStore, _, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        preserves.value rfl valueCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      refine ⟨extension, _, finalStore, .fallthrough, ?_, finalHeap, finalInstalled, lastFrame⟩
      apply Core.LanguageResult.bind_success _ evaluated
      simpa only [← Core.Expr.rename_insertion, rename_fallthrough] using
        Core.LocalLoop.fallthrough_evaluates type (targetValue :: environment) finalStore

/-- A failed RHS leaves the target untouched and skips its cell read/write. -/
theorem assign_fault {statement : Stmt} {lhs rhs : Expr}
    {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (kind : statement.kind = .assign lhs rhs)
    (right : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rhs initial (.fault reason) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro fuel scope result loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, name, path, binding, index, updated, rightCompiled,
          _, _, _, _, _, rfl⟩ := assignment_components compiled
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        right rightCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, _, finalStore, .language reason,
            Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

theorem return_fault {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {reason : Semantics.Fault} (kind : statement.kind = .returnStmt value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.fault reason) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro fuel scope type loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨checked, matched, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      have sameType := expectType_eq_of_ok matched
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        preserves valueCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, _, finalStore, .language reason,
            Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

theorem expression_fault {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {reason : Semantics.Fault} (kind : statement.kind = .expression value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.fault reason) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro fuel scope type loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        preserves valueCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, _, finalStore, .language reason,
            Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

/-- A successful RHS leaves a represented heap. The checked assignment path
therefore has a source update, excluding every malformed assignment outcome. -/
theorem assign_invalid {statement : Stmt} {lhs rhs : Expr}
    {initial middle : Semantics.State σ} {sourceValue : Semantics.Value} {reason : Semantics.Fault}
    (kind : statement.kind = .assign lhs rhs)
    (right : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rhs initial (.value sourceValue) middle)
    (invalid : Semantics.assignResult sourceEnvironment middle lhs sourceValue = .fault reason) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) middle := by
  intro fuel scope result loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, name, path, binding, index, updated, rightCompiled, _⟩ := assignment_components compiled
      obtain ⟨extension, value, middleStore, _, _, middleHeap, _, _⟩ :=
        right.value rfl rightCompiled covered locals globals runtime heap installed
      obtain ⟨finalState, assigned⟩ := assignment_valid (value := sourceValue) compiled covered
        (locals.extendWorld extension) middleHeap.toHeapRel
      rw [invalid] at assigned
      cases assigned

/-- The accepted initializer supplies a source zero value, so a malformed
source declaration cannot occur in a compiled statement list. -/
theorem declare_invalid {statement : Stmt} {rest : List Stmt} {name : String} {type : Ty}
    {state : Semantics.State σ} (kind : statement.kind = .letDecl name type)
    (invalid : Semantics.zero? type = none) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest)
      state (.fault .unsupportedType) state := by
  intro fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨localType, initializer, body, typeCompiled, _⟩ := declaration_components compiled
      obtain ⟨shape, sourceShape, _⟩ := lowerType_shape typeCompiled
      simp [Semantics.zero?, sourceShape] at invalid

theorem declared_invalid {statement : Stmt} {name : String} {type : Ty}
    {state : Semantics.State σ} (kind : statement.kind = .letDecl name type)
    (invalid : Semantics.zero? type = none) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state (.fault .unsupportedType) state := by
  intro fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel => exact declare_invalid rfl invalid compiled

theorem comment {statement : Stmt} {text : String} {state : Semantics.State σ}
    (kind : statement.kind = .comment text) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state .fallthrough state := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    _ _ _ heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      cases compiled
      exact ⟨[], _, store, .fallthrough, Core.LocalLoop.fallthrough_evaluates _ _ _,
        by simpa only [List.append_nil] using heapRelated, installed, ClosuresPreserved.refl store⟩

theorem nil {state : Semantics.State σ} :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment [] state .fallthrough state := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    _ _ _ heapRelated installed
  exact ⟨[], _, store, .fallthrough, empty compiled mapping environment store,
    by simpa only [List.append_nil] using heapRelated, installed, ClosuresPreserved.refl store⟩

theorem declare {statement : Stmt} {rest : List Stmt} {name : String} {sourceType : Ty}
    {sourceValue : Semantics.Value} {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .letDecl name sourceType) (zero : Semantics.zero? sourceType = some sourceValue)
    (tail : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured
      ((name, initial.heap.length) :: sourceEnvironment) rest (Semantics.allocate initial sourceValue).2 control final) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      have allowed := ContextualStatementCorrespondence.declaration_allowed compiled
      obtain ⟨localType, initializer, body, typeCompiled, zeroCompiled, bodyCompiled, rfl⟩ :=
        declaration_components compiled
      obtain ⟨shape, shapeFound, rfl⟩ := lowerType_shape typeCompiled
      have zeroEqual : sourceValue = shape.zero := by
        simpa only [Semantics.zero?, shapeFound, Option.map_some, Option.some.injEq] using zero.symm
      obtain ⟨value, valueRelated, evaluated⟩ := zeroValue_evaluates shape zeroCompiled environment store
      have allocated := heapRelated.allocate (zeroEqual ▸ valueRelated)
      have entry : (world ++ [(coreType shape, store.length)])[initial.heap.length]? =
          some (coreType shape, store.length) := by
        rw [← heapRelated.length_eq, List.getElem?_concat_length]
      have environmentExtended :=
        (environmentRelated.extendWorld [(coreType shape, store.length)]).addLocal
          name (coreType shape) initial.heap.length store.length entry
      have globalsExtended := globalsRelated.addLocal name (coreType shape)
        (.cellRef (Core.OptionalCell.cellType (coreType shape)) store.length) allowed
      obtain ⟨extension, targetValue, finalStore, related, bodyEvaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        tail bodyCompiled (covered.addLocal name (coreType shape) initial.heap.length) environmentExtended globalsExtended
          (runtime.addLocal name (coreType shape) (.cellRef (Core.OptionalCell.cellType (coreType shape)) store.length) allowed) allocated (installed.append _)
      refine ⟨[(coreType shape, store.length)] ++ extension, targetValue, finalStore,
        related, ?_, ?_, finalInstalled, ClosuresPreserved.trans (ClosuresPreserved.append _ _) lastFrame⟩
      · have initialized := Core.OptionalCell.allocateInitialized_evaluates (type := coreType shape) evaluated
        have same := zeroValue_rename shape zeroCompiled mapping
        simpa only [Core.Expr.rename, Core.OptionalCell.allocateInitialized, same] using
          Core.Evaluates.letE initialized bodyEvaluated
      · simpa only [List.append_assoc] using finalHeap

theorem next {statement : Stmt} {rest : List Stmt} {initial middle final : Semantics.State σ}
    {control : Semantics.Control}
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    (head : StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial .fallthrough middle)
    (tail : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rest middle control final) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨first, next, firstCompiled, nextCompiled, rfl⟩ := sequence_components notDeclaration compiled
      obtain ⟨firstExtension, firstValue, middleStore, firstRelated, firstEvaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        head firstCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      cases firstRelated
      have nextEnvironment : EnvironmentRel (world ++ firstExtension) sourceEnvironment scope
          (fun index => mapping index + 3)
          (.unit :: .inLeft type .unit :: .inLeft Core.LocalLoop.transferType (.inLeft type .unit) :: environment) := by
        simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_comm, List.cons_append,
          List.nil_append] using
          (environmentRelated.extendWorld firstExtension).prepend
            [.unit, .inLeft type .unit, .inLeft Core.LocalLoop.transferType (.inLeft type .unit)]
      have nextGlobals : GlobalEnvironmentRel codes locations scope
          (fun index => mapping index + 3)
          (.unit :: .inLeft type .unit :: .inLeft Core.LocalLoop.transferType (.inLeft type .unit) :: environment) := by
        simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_comm, List.cons_append,
          List.nil_append] using globalsRelated.prepend
            [.unit, .inLeft type .unit, .inLeft Core.LocalLoop.transferType (.inLeft type .unit)]
      obtain ⟨extension, targetValue, finalStore, related, nextEvaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        tail nextCompiled covered nextEnvironment nextGlobals
          (by simpa only [Nat.add_comm, List.length_cons, List.length_nil, Nat.zero_add, List.cons_append, List.nil_append]
            using runtime.prepend [.unit, .inLeft type .unit,
              .inLeft Core.LocalLoop.transferType (.inLeft type .unit)]) middleHeap middleInstalled
      exact ⟨firstExtension ++ extension, targetValue, finalStore, related,
        sequence_fallthrough firstEvaluated nextEvaluated,
        by simpa only [List.append_assoc] using finalHeap, finalInstalled, firstFrame.trans lastFrame⟩

theorem stop {statement : Stmt} {rest : List Stmt} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    (head : StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final)
    (stopped : control ≠ .fallthrough) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨first, next, firstCompiled, _, rfl⟩ := sequence_components notDeclaration compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        head firstCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      refine ⟨extension, targetValue, finalStore, related, ?_, finalHeap, finalInstalled, lastFrame⟩
      rw [rename_sequence]
      cases related with
      | fallthrough => exact False.elim (stopped rfl)
      | returned valueRelated => exact Core.LocalLoop.sequence_returned type evaluated
      | breaking => exact Core.LocalLoop.sequence_transfer type evaluated
      | continuing => exact Core.LocalLoop.sequence_transfer type evaluated
      | language => exact Core.LocalLoop.sequence_failure type evaluated

/-- The standalone declaration compiler delegates to its actual singleton
statement-list compiler. The new local remains represented in the final heap. -/
theorem declared {statement : Stmt} {name : String} {type : Ty}
    {value : Semantics.Value} (kind : statement.kind = .letDecl name type)
    (zero : Semantics.zero? type = some value) {initial : Semantics.State σ} :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial
      .fallthrough (Semantics.allocate initial value).2 := by
  intro fuel scope result loops expression compiled covered world mapping environment store
    locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      exact declare rfl zero nil compiled covered locals globals runtime heap installed

theorem block {statement : Stmt} {body : List Stmt}
    {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .block body)
    (continued : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment body initial control final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final := by
  intro fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel => exact continued compiled

theorem breaking {statement : Stmt} {state : Semantics.State σ}
    (kind : statement.kind = .breakStmt) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state .breaking state := by
  intro fuel scope result loops expression compiled covered world mapping environment store _ _ _ heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      cases loops with
      | zero => simp [lowerStatement, fail] at compiled
      | succ loops =>
          simp only [lowerStatement, Nat.add_one_ne_zero, ↓reduceIte] at compiled
          cases compiled
          exact ⟨[], _, store, .breaking, Core.LocalLoop.breaking_evaluates _ _ _,
            by simpa only [List.append_nil] using heap, installed, ClosuresPreserved.refl store⟩

theorem continuing {statement : Stmt} {state : Semantics.State σ}
    (kind : statement.kind = .continueStmt) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state .continuing state := by
  intro fuel scope result loops expression compiled covered world mapping environment store _ _ _ heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      cases loops with
      | zero => simp [lowerStatement, fail] at compiled
      | succ loops =>
          simp only [lowerStatement, Nat.add_one_ne_zero, ↓reduceIte] at compiled
          cases compiled
          exact ⟨[], _, store, .continuing, Core.LocalLoop.continuing_evaluates _ _ _,
            by simpa only [List.append_nil] using heap, installed, ClosuresPreserved.refl store⟩

end Solcore.Frontend.RustHull.DerivationStatementCorrespondence
