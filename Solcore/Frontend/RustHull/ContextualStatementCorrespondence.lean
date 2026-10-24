import Solcore.Frontend.RustHull.NamedCallCorrespondence

/-! Straight-line source execution with installed global functions. Lexical
function references and installed closures survive local allocation, writes
and administrative statement-sequencing binders. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContextualStatementCorrespondence
open Correspondence StatementCorrespondence NamedCallCorrespondence

theorem declaration_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {name : String} {type : Ty} {span : Option Span}
    {rest : List Stmt} {expression : Core.Expr}
    (compiled : lowerStatements (fuel + 1) signatures scope result loops
      (⟨.letDecl name type, span⟩ :: rest) = .ok expression) :
    name.startsWith Effects.reservedPrefix = false := by
  cases allowed : name.startsWith Effects.reservedPrefix with
  | false => rfl
  | true => simp [lowerStatements, allowed, fail, Bind.bind, Except.bind] at compiled

theorem assign_variable {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {rhs : Expr} (rightPreserves : ContextualExprPreserves functions effects signatures codes locations captured rhs)
    {sourceEnvironment : Semantics.Environment} {initial middle final : Semantics.State σ}
    {sourceValue : Semantics.Value} {sourceType : Ty} {name : String}
    {leftSpan statementSpan : Option Span}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment rhs initial
      (.value sourceValue) middle)
    (assigned : Semantics.assignResult sourceEnvironment middle
      ⟨sourceType, .var name, leftSpan⟩ sourceValue = .value final)
    {fuel : Nat} {scope : Scope} {result : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign ⟨sourceType, .var name, leftSpan⟩ rhs, statementSpan⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue result) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  obtain ⟨right, binding, index, rightCompiled, looked, _, sameType, rfl⟩ :=
    assign_variable_components compiled
  obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleInstalled⟩ :=
    rightPreserves sourceEvaluated rightCompiled environmentRelated globalsRelated heapRelated installed
  rw [sameType] at valueRelated
  obtain ⟨sourceLocation, old, found, read, rfl⟩ := assign_variable_source assigned
  have middleEnvironment := environmentRelated.extendWorld extension
  obtain ⟨location, entry, _, targetFound⟩ :=
    middleEnvironment name sourceLocation binding index found looked
  obtain ⟨oldValue, targetRead, _⟩ := middleHeap.read entry read
  have written : middleStore.write? location (.inRight .unit value) =
      some (middleStore.set location (.inRight .unit value)) :=
    Core.Store.write?_eq_some_iff.mpr ⟨middleHeap.location_bound entry, rfl⟩
  exact ⟨extension, _, assign_variable_core evaluated targetFound targetRead written,
    middleHeap.write entry valueRelated written,
    middleInstalled.write middleHeap entry written⟩

theorem returned {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {value : Expr}
    (preserves : ContextualExprPreserves functions effects signatures codes locations captured value)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment value initial
      (.value sourceValue) final)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {span : Option Span}
    {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope type loops
      ⟨.returnStmt value, span⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ControlRel type (.returned sourceValue) targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  have components := compiled
  simp only [lowerStatement] at components
  obtain ⟨lowered, valueCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨checked, matched, _⟩ := lower_bind_eq_ok.mp components
  cases checked
  have sameType := expectType_eq_of_ok matched
  obtain ⟨extension, targetValue, finalStore, valueRelated, evaluated, finalHeap, finalInstalled⟩ :=
    preserves sourceEvaluated valueCompiled environmentRelated globalsRelated heapRelated installed
  exact ⟨extension, Core.LocalLoop.returnedValue targetValue, finalStore,
    .returned (sameType ▸ valueRelated), return_success compiled valueCompiled evaluated,
    finalHeap, finalInstalled⟩

theorem expression_statement {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {value : Expr}
    (preserves : ContextualExprPreserves functions effects signatures codes locations captured value)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment value initial
      (.value sourceValue) final)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {span : Option Span}
    {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope type loops
      ⟨.expression value, span⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue type) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  simp only [lowerStatement] at compiled
  obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  obtain ⟨extension, targetValue, finalStore, _, evaluated, finalHeap, finalInstalled⟩ :=
    preserves sourceEvaluated valueCompiled environmentRelated globalsRelated heapRelated installed
  refine ⟨extension, finalStore, ?_, finalHeap, finalInstalled⟩
  apply Core.LanguageResult.bind_success _ evaluated
  simpa only [← Core.Expr.rename_insertion, rename_fallthrough] using
    Core.LocalLoop.fallthrough_evaluates type (targetValue :: environment) finalStore

/-- This first statement fragment has no branch or loop construct. Its
expression premises are proved separately against the same source semantics. -/
def StraightLine {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment) (statement : Stmt) : Prop :=
  match statement.kind with
  | .letDecl _ _ | .comment _ => True
  | .assign ⟨_, .var _, _⟩ value | .expression value | .returnStmt value =>
      ContextualExprPreserves functions effects signatures codes locations captured value
  | _ => False

theorem straight_line_statement {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {statement : Stmt} (eligible : StraightLine functions effects signatures codes locations captured statement)
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStmt functions effects sourceEnvironment statement initial control final)
    (normal : NormalControl control)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatement fuel signatures scope type loops statement = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ControlRel type control targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
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
          obtain ⟨extension, finalStore, executed, finalHeap, finalInstalled⟩ :=
            assign_variable eligible evaluated assigned compiled environmentRelated globalsRelated heapRelated installed
          exact ⟨extension, _, finalStore, .fallthrough, executed, finalHeap, finalInstalled⟩
      case expression value sourceValue kind evaluated =>
        cases kind
        obtain ⟨extension, finalStore, executed, finalHeap, finalInstalled⟩ :=
          expression_statement eligible evaluated compiled environmentRelated globalsRelated heapRelated installed
        exact ⟨extension, _, finalStore, .fallthrough, executed, finalHeap, finalInstalled⟩
      case returned value sourceValue kind evaluated =>
        cases kind
        exact returned eligible evaluated compiled environmentRelated globalsRelated heapRelated installed
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
          by simpa only [List.append_nil] using heapRelated, installed⟩

/-- Accepted straight-line statement lists preserve normal source execution,
including each allocation and write. The premise concerns actual independent
source derivations; fuel here bounds compilation, not source execution. -/
theorem straight_line_statements {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    {statements : List Stmt}
    (compiled : lowerStatements fuel signatures scope type loops statements = .ok expression)
    (eligible : ∀ statement ∈ statements, StraightLine functions effects signatures codes locations captured statement)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment statements initial control final)
    (normal : NormalControl control)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ControlRel type control targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  induction fuel generalizing scope type loops expression statements sourceEnvironment initial final control
      world mapping environment store with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel ih =>
      cases sourceEvaluated
      case nil =>
        exact ⟨[], _, store, .fallthrough, empty compiled mapping environment store,
          by simpa only [List.append_nil] using heapRelated, installed⟩
      case declare statement rest name sourceType sourceValue kind zero tail =>
        cases statement with | mk statementKind span =>
        cases kind
        have allowed := declaration_allowed compiled
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
        obtain ⟨extension, targetValue, finalStore, related, bodyEvaluated, finalHeap, finalInstalled⟩ :=
          ih bodyCompiled (fun statement member => eligible statement (List.mem_cons_of_mem _ member))
            tail normal environmentExtended globalsExtended allocated (installed.append _)
        refine ⟨[(coreType shape, store.length)] ++ extension, targetValue, finalStore,
          related, ?_, ?_, finalInstalled⟩
        · have initialized := Core.OptionalCell.allocateInitialized_evaluates
            (type := coreType shape) evaluated
          have same := zeroValue_rename shape zeroCompiled mapping
          simpa only [Core.Expr.rename, Core.OptionalCell.allocateInitialized, same] using
            Core.Evaluates.letE initialized bodyEvaluated
        · simpa only [List.append_assoc] using finalHeap
      case declareInvalid => contradiction
      case next statement rest middle notDeclaration head tail =>
        obtain ⟨first, next, firstCompiled, nextCompiled, rfl⟩ := sequence_components notDeclaration compiled
        obtain ⟨firstExtension, firstValue, middleStore, firstRelated, firstEvaluated, middleHeap, middleInstalled⟩ :=
          straight_line_statement (eligible statement (List.mem_cons_self ..)) notDeclaration
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
        obtain ⟨extension, targetValue, finalStore, related, nextEvaluated, finalHeap, finalInstalled⟩ :=
          ih nextCompiled (fun statement member => eligible statement (List.mem_cons_of_mem _ member))
            tail normal nextEnvironment nextGlobals middleHeap middleInstalled
        exact ⟨firstExtension ++ extension, targetValue, finalStore, related,
          sequence_fallthrough firstEvaluated nextEvaluated,
          by simpa only [List.append_assoc] using finalHeap, finalInstalled⟩
      case stop statement rest notDeclaration stopped head =>
        obtain ⟨first, next, firstCompiled, _, rfl⟩ := sequence_components notDeclaration compiled
        obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalInstalled⟩ :=
          straight_line_statement (eligible statement (List.mem_cons_self ..)) notDeclaration
            head normal firstCompiled environmentRelated globalsRelated heapRelated installed
        refine ⟨extension, targetValue, finalStore, related, ?_, finalHeap, finalInstalled⟩
        rw [rename_sequence]
        cases related with
        | fallthrough => exact False.elim (stopped rfl)
        | returned valueRelated => exact Core.LocalLoop.sequence_returned type evaluated
        | breaking => contradiction
        | continuing => contradiction
        | language => contradiction

end Solcore.Frontend.RustHull.ContextualStatementCorrespondence
