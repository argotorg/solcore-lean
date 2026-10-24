import Solcore.Frontend.RustHull.ContextualStatementCorrespondence
import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport

/-! Statement steps consume simulation hypotheses for the particular source
subderivations. They do not assume a rank on calls or a universal expression
preservation theorem. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationStatementCorrespondence
open Correspondence StatementCorrespondence DerivationCorrespondence

variable {σ : Type} {signatures : List Signature}
  {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
  {sourceEnvironment : Semantics.Environment}

theorem assign_variable {statement : Stmt} {rhs : Expr} {sourceType : Ty} {name : String}
    {leftSpan : Option Span} {initial middle final : Semantics.State σ} {sourceValue : Semantics.Value}
    (kind : statement.kind = .assign ⟨sourceType, .var name, leftSpan⟩ rhs)
    (right : ExprSimulation signatures codes locations captured sourceEnvironment rhs initial (.value sourceValue) middle)
    (assigned : Semantics.assignResult sourceEnvironment middle
      ⟨sourceType, .var name, leftSpan⟩ sourceValue = .value final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial .fallthrough final := by
  intro _ fuel scope result loops expression compiled world mapping environment store
    environmentRelated globalsRelated heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, binding, index, rightCompiled, looked, _, sameType, rfl⟩ :=
        assign_variable_components compiled
      obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        right.value rfl rightCompiled environmentRelated globalsRelated heapRelated installed
      rw [sameType] at valueRelated
      obtain ⟨sourceLocation, old, found, read, rfl⟩ := assign_variable_source assigned
      obtain ⟨location, entry, _, targetFound⟩ :=
        (environmentRelated.extendWorld extension) name sourceLocation binding index found looked
      obtain ⟨oldValue, targetRead, _⟩ := middleHeap.read entry read
      have written : middleStore.write? location (.inRight .unit value) =
          some (middleStore.set location (.inRight .unit value)) :=
        Core.Store.write?_eq_some_iff.mpr ⟨middleHeap.location_bound entry, rfl⟩
      exact ⟨extension, _, _, .fallthrough, assign_variable_core evaluated targetFound targetRead written,
        middleHeap.write entry valueRelated written, middleInstalled.write middleHeap entry written,
        firstFrame.trans (ClosuresPreserved.write middleHeap entry written)⟩

theorem returned {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value} (kind : statement.kind = .returnStmt value)
    (preserves : ExprSimulation signatures codes locations captured sourceEnvironment value initial (.value sourceValue) final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial (.returned sourceValue) final := by
  intro _ fuel scope type loops expression compiled world mapping environment store
    environmentRelated globalsRelated heapRelated installed
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
        preserves.value rfl valueCompiled environmentRelated globalsRelated heapRelated installed
      exact ⟨extension, Core.LocalLoop.returnedValue targetValue, finalStore,
        .returned (sameType ▸ valueRelated), return_success compiled valueCompiled evaluated,
        finalHeap, finalInstalled, lastFrame⟩

theorem expression_statement {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value} (kind : statement.kind = .expression value)
    (preserves : ExprSimulation signatures codes locations captured sourceEnvironment value initial (.value sourceValue) final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial .fallthrough final := by
  intro _ fuel scope type loops expression compiled world mapping environment store
    environmentRelated globalsRelated heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨extension, targetValue, finalStore, _, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        preserves.value rfl valueCompiled environmentRelated globalsRelated heapRelated installed
      refine ⟨extension, _, finalStore, .fallthrough, ?_, finalHeap, finalInstalled, lastFrame⟩
      apply Core.LanguageResult.bind_success _ evaluated
      simpa only [← Core.Expr.rename_insertion, rename_fallthrough] using
        Core.LocalLoop.fallthrough_evaluates type (targetValue :: environment) finalStore

/-- A failed RHS leaves the target untouched and skips its cell read/write. -/
theorem assign_fault {statement : Stmt} {rhs : Expr} {sourceType : Ty} {name : String}
    {leftSpan : Option Span} {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (kind : statement.kind = .assign ⟨sourceType, .var name, leftSpan⟩ rhs)
    (right : ExprSimulation signatures codes locations captured sourceEnvironment rhs initial (.fault reason) final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro safe fuel scope result loops expression compiled world mapping environment store locals globals heap installed
  obtain ⟨reason, rfl⟩ := (safeControl_fault_iff reason).mp safe
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, binding, index, rightCompiled, _, _, _, rfl⟩ := assign_variable_components compiled
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        right trivial rightCompiled locals globals heap installed
      cases related
      exact ⟨extension, _, finalStore, .language reason,
        Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

theorem return_fault {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {reason : Semantics.Fault} (kind : statement.kind = .returnStmt value)
    (preserves : ExprSimulation signatures codes locations captured sourceEnvironment value initial (.fault reason) final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro safe fuel scope type loops expression compiled world mapping environment store locals globals heap installed
  obtain ⟨reason, rfl⟩ := (safeControl_fault_iff reason).mp safe
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
        preserves trivial valueCompiled locals globals heap installed
      cases related
      exact ⟨extension, _, finalStore, .language reason,
        Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

theorem expression_fault {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {reason : Semantics.Fault} (kind : statement.kind = .expression value)
    (preserves : ExprSimulation signatures codes locations captured sourceEnvironment value initial (.fault reason) final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro safe fuel scope type loops expression compiled world mapping environment store locals globals heap installed
  obtain ⟨reason, rfl⟩ := (safeControl_fault_iff reason).mp safe
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        preserves trivial valueCompiled locals globals heap installed
      cases related
      exact ⟨extension, _, finalStore, .language reason,
        Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

theorem assignment_not_language {τ : Type} (env : Semantics.Environment) (state : Semantics.State τ)
    (lhs : Expr) (value : Semantics.Value) (reason : Core.Word) :
    Semantics.assignResult env state lhs value ≠ .fault (.language reason) := by
  unfold Semantics.assignResult
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · split <;> simp

theorem comment {statement : Stmt} {text : String} {state : Semantics.State σ}
    (kind : statement.kind = .comment text) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement state .fallthrough state := by
  intro _ fuel scope type loops expression compiled world mapping environment store
    _ _ heapRelated installed
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
    StatementsSimulation signatures codes locations captured sourceEnvironment [] state .fallthrough state := by
  intro _ fuel scope type loops expression compiled world mapping environment store
    _ _ heapRelated installed
  exact ⟨[], _, store, .fallthrough, empty compiled mapping environment store,
    by simpa only [List.append_nil] using heapRelated, installed, ClosuresPreserved.refl store⟩

theorem declare {statement : Stmt} {rest : List Stmt} {name : String} {sourceType : Ty}
    {sourceValue : Semantics.Value} {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .letDecl name sourceType) (zero : Semantics.zero? sourceType = some sourceValue)
    (tail : StatementsSimulation signatures codes locations captured
      ((name, initial.heap.length) :: sourceEnvironment) rest (Semantics.allocate initial sourceValue).2 control final) :
    StatementsSimulation signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro normal fuel scope type loops expression compiled world mapping environment store
    environmentRelated globalsRelated heapRelated installed
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
        tail normal bodyCompiled environmentExtended globalsExtended allocated (installed.append _)
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
    (head : StmtSimulation signatures codes locations captured sourceEnvironment statement initial .fallthrough middle)
    (tail : StatementsSimulation signatures codes locations captured sourceEnvironment rest middle control final) :
    StatementsSimulation signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro normal fuel scope type loops expression compiled world mapping environment store
    environmentRelated globalsRelated heapRelated installed
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨first, next, firstCompiled, nextCompiled, rfl⟩ := sequence_components notDeclaration compiled
      obtain ⟨firstExtension, firstValue, middleStore, firstRelated, firstEvaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        head trivial firstCompiled environmentRelated globalsRelated heapRelated installed
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
        tail normal nextCompiled nextEnvironment nextGlobals middleHeap middleInstalled
      exact ⟨firstExtension ++ extension, targetValue, finalStore, related,
        sequence_fallthrough firstEvaluated nextEvaluated,
        by simpa only [List.append_assoc] using finalHeap, finalInstalled, firstFrame.trans lastFrame⟩

theorem stop {statement : Stmt} {rest : List Stmt} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    (head : StmtSimulation signatures codes locations captured sourceEnvironment statement initial control final)
    (stopped : control ≠ .fallthrough) :
    StatementsSimulation signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro normal fuel scope type loops expression compiled world mapping environment store
    environmentRelated globalsRelated heapRelated installed
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨first, next, firstCompiled, _, rfl⟩ := sequence_components notDeclaration compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        head normal firstCompiled environmentRelated globalsRelated heapRelated installed
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
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial
      .fallthrough (Semantics.allocate initial value).2 := by
  intro normal fuel scope result loops expression compiled world mapping environment store
    locals globals heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      exact declare rfl zero nil normal compiled locals globals heap installed

theorem block {statement : Stmt} {body : List Stmt}
    {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .block body)
    (continued : StatementsSimulation signatures codes locations captured sourceEnvironment body initial control final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial control final := by
  intro safe fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel => exact continued safe compiled

theorem breaking {statement : Stmt} {state : Semantics.State σ}
    (kind : statement.kind = .breakStmt) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement state .breaking state := by
  intro _ fuel scope result loops expression compiled world mapping environment store _ _ heap installed
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
    StmtSimulation signatures codes locations captured sourceEnvironment statement state .continuing state := by
  intro _ fuel scope result loops expression compiled world mapping environment store _ _ heap installed
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
