import Solcore.Frontend.RustHull.LoweringSafety
import Solcore.Frontend.RustHull.SemanticsCorrespondenceSupport
import Solcore.Frontend.RustHull.SemanticsTypeCorrespondence
import Solcore.Core.Derived

/-! Operational correspondence for the actual Hull statement lowering. The
renaming parameter accounts for administrative Core binders without assuming
that closures stored by an earlier computation have unchanged captures. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence

open Correspondence

/-- Normal expression correspondence supplies the expression induction premise
used by statement sequencing. The external projection is explicit; this does
not assume that an arbitrary external operation preserves its state. -/
def NormalExprPreserves {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (signatures : List Signature)
    (external : σ → Core.Store → Prop) (expression : Expr) : Prop :=
  ∀ {sourceEnvironment initial final sourceValue},
    Semantics.EvalExpr functions effects sourceEnvironment expression initial
      (.value sourceValue) final →
    ∀ {fuel scope lowered}, lowerExpression fuel signatures scope expression = .ok lowered →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      HeapRel world initial.heap store → external initial.external store →
      ∃ extension targetValue finalStore,
        ValueRel lowered.type sourceValue targetValue ∧
        Core.Evaluates environment store (lowered.expression.rename mapping)
          (.inRight .word targetValue) finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore

/-- A local cell is disjoint from the external-state projection when allocating
or writing that cell leaves the projection unchanged. -/
structure ExternalFrame {σ : Type} (external : σ → Core.Store → Prop) : Prop where
  allocate : ∀ {state store type value}, external state store →
    external state (store ++ [Core.Value.inRight type value])
  write : ∀ {state} {world : World} {source : Semantics.Heap} {store : Core.Store}
    {index : Nat} {type : Core.Ty} {location : Nat} {value : Core.Value} {updated : Core.Store},
    external state store → HeapRel world source store →
    world[index]? = some (type, location) →
    store.write? location (.inRight .unit value) = some updated → external state updated

/-- Source control has a fixed observable Core envelope. Invalid source
operations have no representation; language faults preserve their reason. -/
inductive ControlRel (type : Core.Ty) : Semantics.Control → Core.Value → Prop where
  | fallthrough : ControlRel type .fallthrough (Core.LocalLoop.fallthroughValue type)
  | returned {source : Semantics.Value} {target : Core.Value}
      (related : ValueRel type source target) :
      ControlRel type (.returned source) (Core.LocalLoop.returnedValue target)
  | breaking : ControlRel type .breaking (Core.LocalLoop.breakingValue type)
  | continuing : ControlRel type .continuing (Core.LocalLoop.continuingValue type)
  | language (reason : Core.Word) :
      ControlRel type (.fault (.language reason))
        (.inLeft (Core.LocalLoop.controlType type) (.word reason))

theorem ControlRel.functional {type : Core.Ty} {source : Semantics.Control}
    {left right : Core.Value} (leftRelated : ControlRel type source left)
    (rightRelated : ControlRel type source right) : left = right := by
  cases leftRelated <;> cases rightRelated <;> first
    | rfl
    | congr 1; exact ValueRel.functional ‹_› ‹_›

theorem declaration_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {name : String} {type : Ty} {span : Option Span}
    {rest : List Stmt} {expression : Core.Expr}
    (compiled : lowerStatements (fuel + 1) signatures scope result loops
      (⟨.letDecl name type, span⟩ :: rest) = .ok expression) :
    ∃ loweredType zero body,
      lowerType fuel type = .ok loweredType ∧ zeroValue loweredType = .ok zero ∧
      lowerStatements fuel signatures (scope.addLocal name loweredType) result loops rest = .ok body ∧
      expression = .letE (Core.OptionalCell.allocateInitialized loweredType zero) body := by
  by_cases reserved : name.startsWith Effects.reservedPrefix
  · simp [lowerStatements, reserved, fail, Bind.bind, Except.bind] at compiled
  · simp only [lowerStatements, reserved, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind] at compiled
    obtain ⟨loweredType, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨zero, zeroCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨body, bodyCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
    cases returned
    exact ⟨loweredType, zero, body, typeCompiled, zeroCompiled, bodyCompiled, rfl⟩

theorem variable_type {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {type : Ty} {name : String} {span : Option Span} {lowered : Lowered}
    {binding : Binding} {index : Nat}
    (compiled : lowerExpression fuel signatures scope ⟨type, .var name, span⟩ = .ok lowered)
    (found : scope.lookup name = .ok (binding, index)) : lowered.type = binding.type := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression] at compiled
      obtain ⟨expected, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      by_cases reserved : name.startsWith Effects.reservedPrefix
      · simp [reserved, fail, Bind.bind, Except.bind] at compiled
      · simp only [reserved, Bool.false_eq_true, ↓reduceIte, Scope.read, found,
          Bind.bind, Except.bind, Pure.pure] at compiled
        obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        cases returned
        rfl

theorem variable_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {type : Ty} {name : String} {span : Option Span} {lowered : Lowered}
    (compiled : lowerExpression fuel signatures scope ⟨type, .var name, span⟩ = .ok lowered) :
    ∃ binding index, scope.lookup name = .ok (binding, index) ∧
      lowered = ⟨binding.type, if binding.reference then
        Core.OptionalCell.read binding.type (.var index) (Core.Word.ofNatModulo 1)
        else Core.LanguageResult.success (.var index)⟩ := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression] at compiled
      obtain ⟨expected, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      by_cases reserved : name.startsWith Effects.reservedPrefix
      · simp [reserved, fail, Bind.bind, Except.bind] at compiled
      · cases found : scope.lookup name with
        | error error =>
            simp [reserved, Scope.read, found, Bind.bind, Except.bind] at compiled
        | ok pair =>
            rcases pair with ⟨binding, index⟩
            simp only [reserved, Bool.false_eq_true, ↓reduceIte, Scope.read, found,
              Bind.bind, Except.bind, Pure.pure] at compiled
            obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
            cases checked
            cases returned
            exact ⟨binding, index, rfl, rfl⟩

/-- A successful source variable read observes the cell selected by the actual
compiler scope. Both the value and the unchanged heap are determined here. -/
theorem variable_evaluates {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {type : Ty} {name : String} {span : Option Span} {lowered : Lowered}
    (compiled : lowerExpression fuel signatures scope ⟨type, .var name, span⟩ = .ok lowered)
    {world : World} {sourceEnvironment : Semantics.Environment}
    {sourceHeap : Semantics.Heap} {sourceLocation : Nat} {sourceValue : Semantics.Value}
    {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world sourceHeap store)
    (found : Semantics.lookupLocation sourceEnvironment name = some sourceLocation)
    (read : sourceHeap[sourceLocation]? = some sourceValue) :
    ∃ targetValue, ValueRel lowered.type sourceValue targetValue ∧
      Core.Evaluates environment store (lowered.expression.rename mapping)
        (.inRight .word targetValue) store := by
  obtain ⟨binding, index, looked, rfl⟩ := variable_components compiled
  obtain ⟨location, targetValue, reference, targetFound, targetRead, valueRelated⟩ :=
    environmentRelated.read heapRelated found looked read
  refine ⟨targetValue, valueRelated, ?_⟩
  simp only [reference, ↓reduceIte]
  exact Core.OptionalCell.read_success (Core.Word.ofNatModulo 1) (.var targetFound) targetRead

theorem assign_variable_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {sourceType : Ty} {name : String}
    {leftSpan statementSpan : Option Span} {rhs : Expr} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign ⟨sourceType, .var name, leftSpan⟩ rhs, statementSpan⟩ = .ok expression) :
    ∃ right binding index,
      lowerExpression fuel signatures scope rhs = .ok right ∧
      scope.lookup name = .ok (binding, index) ∧ binding.reference = true ∧
      right.type = binding.type ∧
      expression = Core.LanguageResult.bind (Core.LocalLoop.controlType result) right.expression
        (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
          (Core.OptionalCell.read binding.type (.var (index + 1)) (Core.Word.ofNatModulo 1))
          (.letE (.storeCell (.var (index + 2)) (.inRight .unit (.var 1)))
            (Core.LocalLoop.fallthrough result))) := by
  simp only [lowerStatement] at compiled
  obtain ⟨left, leftCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨right, rightCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, matched, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  cases fuel with
  | zero => simp [lowerExpression, fail] at leftCompiled
  | succ fuel =>
      simp only [place, Bind.bind, Except.bind, Pure.pure] at compiled
      obtain ⟨⟨binding, index⟩, found, compiled⟩ := lower_bind_eq_ok.mp compiled
      have reference : binding.reference = true := by
        cases yes : binding.reference
        · simp [yes, fail] at compiled
        · rfl
      simp only [reference, ↓reduceIte, updateProduct, Pure.pure] at compiled
      cases compiled
      refine ⟨right, binding, index, rightCompiled, found, reference, ?_, rfl⟩
      exact (expectType_eq_of_ok matched).symm.trans (variable_type leftCompiled found)

theorem assign_variable_source {σ : Type} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {sourceType : Ty} {name : String}
    {span : Option Span} {value : Semantics.Value}
    (assigned : Semantics.assignResult sourceEnvironment initial
      ⟨sourceType, .var name, span⟩ value = .value final) :
    ∃ location old, Semantics.lookupLocation sourceEnvironment name = some location ∧
      initial.heap[location]? = some old ∧
      final = {initial with heap := initial.heap.set location value} := by
  simp only [Semantics.assignResult, Semantics.place?] at assigned
  cases found : Semantics.lookupLocation sourceEnvironment name with
  | none => simp only [found] at assigned; contradiction
  | some location =>
      cases read : initial.heap[location]? with
      | none => simp only [found, read] at assigned; contradiction
      | some old =>
          have bound := (List.getElem?_eq_some_iff.mp read).1
          simp only [found, read, Semantics.updateProduct?, Semantics.write?, bound,
            ↓reduceIte, Semantics.Result.value.injEq] at assigned
          exact ⟨location, old, rfl, read, assigned.symm⟩

/-- The assignment read occurs after the RHS computation. In particular, a
call in the RHS may have updated the old root before this write is performed. -/
theorem assign_variable_core {result type : Core.Ty} {rhs : Core.Expr} {index : Nat}
    {mapping : Core.Renaming} {environment : Core.Environment}
    {initial middle final : Core.Store} {value old : Core.Value} {location : Nat}
    (evaluated : Core.Evaluates environment initial (rhs.rename mapping)
      (.inRight .word value) middle)
    (found : environment[mapping index]? =
      some (.cellRef (Core.OptionalCell.cellType type) location))
    (read : middle.read? location = some (.inRight .unit old))
    (written : middle.write? location (.inRight .unit value) = some final) :
    Core.Evaluates environment initial
      ((Core.LanguageResult.bind (Core.LocalLoop.controlType result) rhs
        (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
          (Core.OptionalCell.read type (.var (index + 1)) (Core.Word.ofNatModulo 1))
          (.letE (.storeCell (.var (index + 2)) (.inRight .unit (.var 1)))
            (Core.LocalLoop.fallthrough result)))).rename mapping)
      (Core.LocalLoop.fallthroughValue result) final := by
  change Core.Evaluates environment initial
    (Core.LanguageResult.bind (Core.LocalLoop.controlType result) (rhs.rename mapping)
      (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
        (Core.OptionalCell.read type (.var (mapping index + 1)) (Core.Word.ofNatModulo 1))
        (.letE (.storeCell (.var (mapping index + 2)) (.inRight .unit (.var 1)))
          (Core.LocalLoop.fallthrough result)))) _ _
  apply Core.LanguageResult.bind_success _ evaluated
  have foundOne : (value :: environment)[mapping index + 1]? =
      some (.cellRef (Core.OptionalCell.cellType type) location) := found
  apply Core.LanguageResult.bind_success _
    (Core.OptionalCell.read_success _ (.var foundOne) read)
  have foundTwo : (old :: value :: environment)[mapping index + 2]? =
      some (.cellRef (Core.OptionalCell.cellType type) location) := found
  exact .letE (.storeCell (.var foundTwo) read (.inRight (.var rfl)) written)
    (Core.LocalLoop.fallthrough_evaluates _ _ _)

/-- Normal assignment preserves the independently specified source heap update
and external effects of its RHS, using the actual accepted Core statement. -/
theorem assign_variable {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {rhs : Expr} (rightPreserves : NormalExprPreserves functions effects signatures external rhs)
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
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue result) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  obtain ⟨right, binding, index, rightCompiled, looked, _, sameType, rfl⟩ :=
    assign_variable_components compiled
  obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleExternal⟩ :=
    rightPreserves sourceEvaluated rightCompiled environmentRelated heapRelated externalRelated
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
    frame.write middleExternal middleHeap entry written⟩

/-- A successful finite zero initializer contains no free Core variables. -/
theorem zeroValue_rename (shape : Semantics.Shape) {expression : Core.Expr}
    (compiled : zeroValue (coreType shape) = .ok expression) (mapping : Core.Renaming) :
    expression.rename mapping = expression := by
  induction shape generalizing expression with
  | word => cases compiled; rfl
  | bool => cases compiled; rfl
  | unit => cases compiled; rfl
  | product left right leftIH rightIH =>
      simp only [coreType, zeroValue] at compiled
      obtain ⟨leftCode, leftCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨rightCode, rightCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      simp only [Core.Expr.rename, leftIH leftCompiled, rightIH rightCompiled]
  | sum left right leftIH _ =>
      simp only [coreType, zeroValue] at compiled
      obtain ⟨leftCode, leftCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      simp only [Core.Expr.rename, leftIH leftCompiled]

@[simp] theorem rename_fallthrough (type : Core.Ty) (mapping : Core.Renaming) :
    (Core.LocalLoop.fallthrough type).rename mapping = Core.LocalLoop.fallthrough type := by
  rfl

@[simp] theorem rename_returnValue (type : Core.Ty) (expression : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalLoop.returnValue type expression).rename mapping =
      Core.LocalLoop.returnValue type (expression.rename mapping) := by
  rfl

@[simp] theorem rename_sequence (type : Core.Ty) (first next : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalLoop.sequence type first next).rename mapping =
      Core.LocalLoop.sequence type (first.rename mapping) (next.rename mapping) := by
  simp [Core.LocalLoop.sequence, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.LocalLoop.returned, Core.Expr.rename, Core.Renaming.lift]

/-- The continuation of an ordinary sequence sees three administrative values.
Its source scope is unchanged; only the Core lookup indices move. -/
theorem weaken_three (expression : Core.Expr) (mapping : Core.Renaming) :
    (((expression.rename mapping).weakenAt 0).weakenAt 0).weakenAt 0 =
      expression.rename (fun index => mapping index + 3) := by
  simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
  congr 1

/-- Empty source lists compile and execute as fallthrough in every scope. -/
theorem empty {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatements fuel signatures scope type loops [] = .ok expression)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (expression.rename mapping)
      (Core.LocalLoop.fallthroughValue type) store := by
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      simp only [lowerStatements] at compiled
      cases compiled
      exact Core.LocalLoop.fallthrough_evaluates _ _ _

/-- A returned payload is connected to the actual statement compiler result.
The expression theorem supplies its evaluation under the same lookup mapping. -/
theorem return_success {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {type : Core.Ty} {loops : Nat} {value : Expr} {span : Option Span}
    {expression : Core.Expr} {lowered : Lowered}
    (compiled : lowerStatement (fuel + 1) signatures scope type loops
      ⟨.returnStmt value, span⟩ = .ok expression)
    (valueCompiled : lowerExpression fuel signatures scope value = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment}
    {initial final : Core.Store} {payload : Core.Value}
    (evaluated : Core.Evaluates environment initial (lowered.expression.rename mapping)
      (.inRight .word payload) final) :
    Core.Evaluates environment initial (expression.rename mapping)
      (Core.LocalLoop.returnedValue payload) final := by
  simp only [lowerStatement, valueCompiled, Bind.bind, Except.bind] at compiled
  obtain ⟨checkedUnit, accepted, returned⟩ := lower_bind_eq_ok.mp compiled
  cases checkedUnit
  cases returned
  exact Core.LocalLoop.returnValue_success type evaluated

theorem returned {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} {value : Expr}
    (preserves : NormalExprPreserves functions effects signatures external value)
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
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ControlRel type (.returned sourceValue) targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  have components := compiled
  simp only [lowerStatement] at components
  obtain ⟨lowered, valueCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨checked, matched, _⟩ := lower_bind_eq_ok.mp components
  cases checked
  have sameType := expectType_eq_of_ok matched
  obtain ⟨extension, targetValue, finalStore, valueRelated, evaluated, finalHeap, finalExternal⟩ :=
    preserves sourceEvaluated valueCompiled environmentRelated heapRelated externalRelated
  exact ⟨extension, Core.LocalLoop.returnedValue targetValue, finalStore,
    .returned (sameType ▸ valueRelated), return_success compiled valueCompiled evaluated,
    finalHeap, finalExternal⟩

theorem expression_statement {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} {value : Expr}
    (preserves : NormalExprPreserves functions effects signatures external value)
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
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue type) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  simp only [lowerStatement] at compiled
  obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  obtain ⟨extension, targetValue, finalStore, _, evaluated, finalHeap, finalExternal⟩ :=
    preserves sourceEvaluated valueCompiled environmentRelated heapRelated externalRelated
  refine ⟨extension, finalStore, ?_, finalHeap, finalExternal⟩
  apply Core.LanguageResult.bind_success _ evaluated
  simpa only [← Core.Expr.rename_insertion, rename_fallthrough] using
    Core.LocalLoop.fallthrough_evaluates type (targetValue :: environment) finalStore

/-- Statement-list sequencing uses the generated expression and preserves the
exact intermediate and final stores. No replacement statement compiler occurs. -/
theorem sequence_fallthrough {type : Core.Ty} {first next : Core.Expr}
    {mapping : Core.Renaming} {environment : Core.Environment}
    {initial middle final : Core.Store} {result : Core.Value}
    (firstEvaluated : Core.Evaluates environment initial (first.rename mapping)
      (Core.LocalLoop.fallthroughValue type) middle)
    (nextEvaluated : Core.Evaluates
      (.unit :: .inLeft type .unit :: .inLeft Core.LocalLoop.transferType (.inLeft type .unit) :: environment)
      middle (next.rename (fun index => mapping index + 3)) result final) :
    Core.Evaluates environment initial ((Core.LocalLoop.sequence type first next).rename mapping)
      result final := by
  rw [rename_sequence]
  apply Core.LocalLoop.sequence_fallthrough type firstEvaluated
  simpa only [weaken_three] using nextEvaluated

/-- A declaration allocates the actual zero initializer and extends the source
and Core environments at their respective fresh locations. The continuation
premise is the statement-list induction hypothesis, applied to the real tail. -/
theorem declaration {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {name : String} {sourceType : Ty} {span : Option Span} {rest : List Stmt}
    {sourceValue : Semantics.Value} {control : Semantics.Control}
    (zero : Semantics.zero? sourceType = some sourceValue)
    (tail : Semantics.EvalStatements functions effects
      ((name, initial.heap.length) :: sourceEnvironment) rest
      (Semantics.allocate initial sourceValue).2 control final)
    (continued : Semantics.EvalStatements functions effects
      ((name, initial.heap.length) :: sourceEnvironment) rest
      (Semantics.allocate initial sourceValue).2 control final → ∀ {fuel scope type loops body},
      lowerStatements fuel signatures scope type loops rest = .ok body →
      ∀ {world mapping environment store},
        EnvironmentRel world ((name, initial.heap.length) :: sourceEnvironment) scope mapping environment →
        HeapRel world (Semantics.allocate initial sourceValue).2.heap store →
        external initial.external store →
        ∃ extension targetValue finalStore,
          ControlRel type control targetValue ∧
          Core.Evaluates environment store (body.rename mapping) targetValue finalStore ∧
          HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatements fuel signatures scope type loops
      (⟨.letDecl name sourceType, span⟩ :: rest) = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ControlRel type control targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
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
      obtain ⟨extension, targetValue, finalStore, controlRelated, bodyEvaluated, finalHeap, finalExternal⟩ :=
        continued tail bodyCompiled environmentExtended allocated (frame.allocate externalRelated)
      refine ⟨[(coreType shape, store.length)] ++ extension, targetValue, finalStore,
        controlRelated, ?_, ?_, finalExternal⟩
      · have initialized := Core.OptionalCell.allocateInitialized_evaluates
          (type := coreType shape) evaluated
        have same := zeroValue_rename shape zeroCompiled mapping
        simpa only [Core.Expr.rename, Core.OptionalCell.allocateInitialized, same] using
          Core.Evaluates.letE initialized bodyEvaluated
      · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.StatementCorrespondence
