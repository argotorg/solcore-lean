import Solcore.Frontend.RustHull.StatementCorrespondence

set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence

open Correspondence

/-- This first statement fragment has no branch or loop construct. Its
expression premises are proved separately against the same source semantics. -/
def StraightLine {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (signatures : List Signature)
    (external : σ → Core.Store → Prop) (statement : Stmt) : Prop :=
  match statement.kind with
  | .letDecl _ _ | .comment _ => True
  | .assign ⟨_, .var _, _⟩ value | .expression value | .returnStmt value =>
      NormalExprPreserves functions effects signatures external value
  | _ => False

def NormalControl : Semantics.Control → Prop
  | .fallthrough | .returned _ => True
  | _ => False

theorem straight_line_statement {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {statement : Stmt} (eligible : StraightLine functions effects signatures external statement)
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStmt functions effects sourceEnvironment statement initial control final)
    (normal : NormalControl control)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatement fuel signatures scope type loops statement = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ControlRel type control targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      cases statement with | mk kind span =>
      cases sourceEvaluated <;> simp_all only [NormalControl]
      case assign lhs rhs middle value kind evaluated assigned =>
        cases kind
        cases lhs with | mk lhsType lhsKind lhsSpan =>
        cases lhsKind <;> simp only [StraightLine] at eligible
        all_goals try contradiction
        case var name =>
          obtain ⟨extension, finalStore, executed, finalHeap, finalExternal⟩ :=
            assign_variable frame eligible evaluated assigned compiled environmentRelated heapRelated externalRelated
          exact ⟨extension, _, finalStore, .fallthrough, executed, finalHeap, finalExternal⟩
      case expression value sourceValue kind evaluated =>
        cases kind
        obtain ⟨extension, finalStore, executed, finalHeap, finalExternal⟩ :=
          expression_statement eligible evaluated compiled environmentRelated heapRelated externalRelated
        exact ⟨extension, _, finalStore, .fallthrough, executed, finalHeap, finalExternal⟩
      case returned value sourceValue kind evaluated =>
        cases kind
        exact returned eligible evaluated compiled environmentRelated heapRelated externalRelated
      case block => exact False.elim eligible
      case forInit => exact False.elim eligible
      case forLoop => exact False.elim eligible
      case matchStmt => exact False.elim eligible
      case assembly => exact False.elim eligible
      case revert => exact False.elim eligible
      case comment text kind =>
        cases kind
        simp only [lowerStatement] at compiled
        cases compiled
        exact ⟨[], _, store, .fallthrough, Core.LocalLoop.fallthrough_evaluates _ _ _,
          by simpa only [List.append_nil] using heapRelated, externalRelated⟩

theorem sequence_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {type : Core.Ty} {loops : Nat} {statement : Stmt} {rest : List Stmt}
    {expression : Core.Expr}
    (notDeclaration : ∀ name sourceType, statement.kind ≠ .letDecl name sourceType)
    (compiled : lowerStatements (fuel + 1) signatures scope type loops
      (statement :: rest) = .ok expression) :
    ∃ first next,
      lowerStatement fuel signatures scope type loops statement = .ok first ∧
      lowerStatements fuel signatures scope type loops rest = .ok next ∧
      expression = Core.LocalLoop.sequence type first next := by
  cases statement with | mk kind span =>
  cases kind
  all_goals first
    | exact False.elim (notDeclaration _ _ rfl)
    | simp only [lowerStatements] at compiled
      obtain ⟨first, firstCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨next, nextCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      exact ⟨first, next, firstCompiled, nextCompiled, rfl⟩

/-- Accepted straight-line statement lists preserve normal source execution,
including each allocation and write. The premise concerns actual independent
source derivations; fuel here bounds compilation, not source execution. -/
theorem straight_line_statements {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    {statements : List Stmt}
    (compiled : lowerStatements fuel signatures scope type loops statements = .ok expression)
    (eligible : ∀ statement ∈ statements, StraightLine functions effects signatures external statement)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment statements initial control final)
    (normal : NormalControl control)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ControlRel type control targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  induction fuel generalizing scope type loops expression statements sourceEnvironment initial final control
      world mapping environment store with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel ih =>
      cases sourceEvaluated
      case nil =>
        exact ⟨[], _, store, .fallthrough, empty compiled mapping environment store,
          by simpa only [List.append_nil] using heapRelated, externalRelated⟩
      case declare statement rest name sourceType sourceValue kind zero tail =>
        cases statement with | mk statementKind span =>
        cases kind
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
        obtain ⟨extension, targetValue, finalStore, related, bodyEvaluated, finalHeap, finalExternal⟩ :=
          ih bodyCompiled (fun statement member => eligible statement (List.mem_cons_of_mem _ member))
            tail normal environmentExtended allocated (frame.allocate externalRelated)
        refine ⟨[(coreType shape, store.length)] ++ extension, targetValue, finalStore,
          related, ?_, ?_, finalExternal⟩
        · have initialized := Core.OptionalCell.allocateInitialized_evaluates
            (type := coreType shape) evaluated
          have same := zeroValue_rename shape zeroCompiled mapping
          simpa only [Core.Expr.rename, Core.OptionalCell.allocateInitialized, same] using
            Core.Evaluates.letE initialized bodyEvaluated
        · simpa only [List.append_assoc] using finalHeap
      case declareInvalid => contradiction
      case next statement rest middle notDeclaration head tail =>
        obtain ⟨first, next, firstCompiled, nextCompiled, rfl⟩ := sequence_components notDeclaration compiled
        obtain ⟨firstExtension, firstValue, middleStore, firstRelated, firstEvaluated, middleHeap, middleExternal⟩ :=
          straight_line_statement frame (eligible statement (List.mem_cons_self ..)) notDeclaration
            head trivial firstCompiled environmentRelated heapRelated externalRelated
        cases firstRelated
        have nextEnvironment : EnvironmentRel (world ++ firstExtension) sourceEnvironment scope
            (fun index => mapping index + 3)
            (.unit :: .inLeft type .unit :: .inLeft Core.LocalLoop.transferType (.inLeft type .unit) :: environment) := by
          simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_comm, List.cons_append,
            List.nil_append] using
            (environmentRelated.extendWorld firstExtension).prepend
              [.unit, .inLeft type .unit, .inLeft Core.LocalLoop.transferType (.inLeft type .unit)]
        obtain ⟨extension, targetValue, finalStore, related, nextEvaluated, finalHeap, finalExternal⟩ :=
          ih nextCompiled (fun statement member => eligible statement (List.mem_cons_of_mem _ member))
            tail normal nextEnvironment middleHeap middleExternal
        exact ⟨firstExtension ++ extension, targetValue, finalStore, related,
          sequence_fallthrough firstEvaluated nextEvaluated,
          by simpa only [List.append_assoc] using finalHeap, finalExternal⟩
      case stop statement rest notDeclaration stopped head =>
        obtain ⟨first, next, firstCompiled, _, rfl⟩ := sequence_components notDeclaration compiled
        obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalExternal⟩ :=
          straight_line_statement frame (eligible statement (List.mem_cons_self ..)) notDeclaration
            head normal firstCompiled environmentRelated heapRelated externalRelated
        refine ⟨extension, targetValue, finalStore, related, ?_, finalHeap, finalExternal⟩
        rw [rename_sequence]
        cases related with
        | fallthrough => exact False.elim (stopped rfl)
        | returned valueRelated => exact Core.LocalLoop.sequence_returned type evaluated
        | breaking => contradiction
        | continuing => contradiction
        | language => contradiction

end Solcore.Frontend.RustHull.StatementCorrespondence
