import Solcore.Frontend.RustHull.Safety
import Solcore.Frontend.RustHull.Internal.LoweringFacts
import Solcore.Core.Internal.DerivedForms

/-!
# Expressions and statements

Operational correspondence for expressions, patterns, assignments and straight-line statements in
the actual lowering output.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.StatementCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ProductAssignmentCorrespondence
/-! Product-place assignment reads the current root after RHS evaluation,
updates one selected component, and writes the root back to its original cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence

def fieldType : List Bool → Core.Ty → Option Core.Ty
  | [], type => some type
  | direction :: rest, .product left right => fieldType rest (if direction then right else left)
  | _ :: _, _ => none

theorem fieldType_append (path suffix : List Bool) (type : Core.Ty) :
    fieldType (path ++ suffix) type = (fieldType path type).bind (fieldType suffix) := by
  induction path generalizing type with
  | nil => rfl
  | cons direction rest ih =>
      cases type <;> simp only [List.cons_append, fieldType]
      all_goals first | rfl | exact ih _

theorem place_correspondence {fuel : Nat} {expression : Expr} {name : String} {path : List Bool}
    (compiled : place fuel expression = .ok (name, path)) :
    Semantics.place? expression = some (name, path) := by
  induction fuel generalizing expression name path with
  | zero => simp [place, fail] at compiled
  | succ fuel ih =>
      cases expression with | mk type kind span =>
      cases kind <;> simp only [place] at compiled
      all_goals try { simp [fail] at compiled }
      case var localName => cases compiled; simp only [Semantics.place?]
      case fst operand =>
        obtain ⟨⟨root, route⟩, inner, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        simp only [Semantics.place?, ih inner, Bind.bind, Option.bind, Pure.pure]
      case snd operand =>
        obtain ⟨⟨root, route⟩, inner, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        simp only [Semantics.place?, ih inner, Bind.bind, Option.bind, Pure.pure]

/-- Checking the actual left expression determines the type at the selected
root path; the RHS type is therefore checked at the component being replaced. -/
theorem place_type {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {lowered : Lowered} {name : String} {path : List Bool}
    {binding : Binding} {index : Nat}
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (placed : place fuel expression = .ok (name, path))
    (looked : scope.lookup name = .ok (binding, index)) :
    fieldType path binding.type = some lowered.type := by
  induction fuel generalizing expression lowered name path with
  | zero => simp [place, fail] at placed
  | succ fuel ih =>
      cases expression with | mk type kind span =>
      cases kind <;> simp only [place] at placed
      all_goals try { simp [fail] at placed }
      case var localName =>
        cases placed
        exact congrArg some (variable_type compiled looked).symm
      case fst operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
          lowerExpression_projection_components false compiled
        have selected := ih operandCompiled innerPlace looked
        rw [operandType] at selected
        rw [fieldType_append, selected]
        rfl
      case snd operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
          lowerExpression_projection_components true compiled
        have selected := ih operandCompiled innerPlace looked
        rw [operandType] at selected
        rw [fieldType_append, selected]
        rfl

/-- Updating a checked path changes only that product component. The two
operands are already computed values, so rebuilding the product is store-free. -/
theorem updateProduct_evaluates {path : List Bool} {type selectedType : Core.Ty}
    {old value expression : Core.Expr}
    (compiled : updateProduct path type old value = .ok expression)
    (selected : fieldType path type = some selectedType)
    {sourceOld sourceValue sourceUpdated : Semantics.Value}
    {targetOld targetValue : Core.Value}
    (oldRelated : ValueRel type sourceOld targetOld)
    (valueRelated : ValueRel selectedType sourceValue targetValue)
    (updated : Semantics.updateProduct? path sourceOld sourceValue = some sourceUpdated)
    {environment : Core.Environment} {store : Core.Store}
    (oldEvaluated : Core.Evaluates environment store old targetOld store)
    (valueEvaluated : Core.Evaluates environment store value targetValue store) :
    ∃ targetUpdated, ValueRel type sourceUpdated targetUpdated ∧
      Core.Evaluates environment store expression targetUpdated store := by
  induction path generalizing type sourceOld sourceUpdated targetOld old expression with
  | nil =>
      cases compiled
      cases selected
      cases updated
      exact ⟨targetValue, valueRelated, valueEvaluated⟩
  | cons direction rest ih =>
      cases type <;> simp only [fieldType] at selected
      all_goals try contradiction
      case product leftType rightType =>
        cases oldRelated with
        | pair leftRelated rightRelated =>
            rename_i sourceLeft sourceRight targetLeft targetRight
            cases direction
            · simp only [updateProduct, Bool.false_eq_true, ↓reduceIte] at compiled
              obtain ⟨component, componentCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
              cases returned
              cases inner : Semantics.updateProduct? rest sourceLeft sourceValue with
              | none => simp [Semantics.updateProduct?, inner] at updated
              | some sourceComponent =>
                  simp only [Semantics.updateProduct?, Bool.false_eq_true, ↓reduceIte, inner,
                    Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at updated
                  cases updated
                  obtain ⟨targetComponent, related, evaluated⟩ :=
                    ih componentCompiled selected leftRelated inner (.first oldEvaluated)
                  exact ⟨.pair targetComponent targetRight, .pair related rightRelated,
                    .pair evaluated (.second oldEvaluated)⟩
            · simp only [updateProduct, ↓reduceIte] at compiled
              obtain ⟨component, componentCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
              cases returned
              cases inner : Semantics.updateProduct? rest sourceRight sourceValue with
              | none => simp [Semantics.updateProduct?, inner] at updated
              | some sourceComponent =>
                  simp only [Semantics.updateProduct?, ↓reduceIte, inner,
                    Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at updated
                  cases updated
                  obtain ⟨targetComponent, related, evaluated⟩ :=
                    ih componentCompiled selected rightRelated inner (.second oldEvaluated)
                  exact ⟨.pair targetLeft targetComponent, .pair leftRelated related,
                    .pair (.first oldEvaluated) evaluated⟩

theorem updateProduct_rename {path : List Bool} {type : Core.Ty} {old value expression : Core.Expr}
    (compiled : updateProduct path type old value = .ok expression) (mapping : Core.Renaming) :
    updateProduct path type (old.rename mapping) (value.rename mapping) = .ok (expression.rename mapping) := by
  induction path generalizing type old expression with
  | nil => cases compiled; rfl
  | cons direction rest ih =>
      cases type <;> simp only [updateProduct] at compiled
      all_goals try { simp [fail] at compiled }
      case product left right =>
        cases direction <;> simp only [Bool.false_eq_true, ↓reduceIte] at compiled
        all_goals
          obtain ⟨component, componentCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
          cases returned
          have renamed := ih componentCompiled
          simp only [Core.Expr.rename] at renamed
          simp only [updateProduct, Bool.false_eq_true, ↓reduceIte, Core.Expr.rename,
            renamed, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem assignment_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {lhs rhs : Expr} {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression) :
    ∃ right name path binding index updated,
      lowerExpression fuel signatures scope rhs = .ok right ∧
      Semantics.place? lhs = some (name, path) ∧
      scope.lookup name = .ok (binding, index) ∧ binding.reference = true ∧
      fieldType path binding.type = some right.type ∧
      updateProduct path binding.type (.var 0) (.var 1) = .ok updated ∧
      expression = Core.LanguageResult.bind (Core.LocalLoop.controlType result) right.expression
        (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
          (Core.OptionalCell.read binding.type (.var (index + 1)) (Core.Word.ofNatModulo 1))
          (.letE (.storeCell (.var (index + 2)) (.inRight .unit updated))
            (Core.LocalLoop.fallthrough result))) := by
  simp only [lowerStatement] at compiled
  obtain ⟨left, leftCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨right, rightCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, matched, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨⟨name, path⟩, placed, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  have reference : binding.reference = true := by
    cases yes : binding.reference
    · simp [yes, fail, Bind.bind, Except.bind] at compiled
    · rfl
  simp only [reference, ↓reduceIte] at compiled
  obtain ⟨updated, updatedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  have selected := place_type leftCompiled placed looked
  rw [expectType_eq_of_ok matched] at selected
  exact ⟨right, name, path, binding, index, updated, rightCompiled,
    place_correspondence placed, looked, reference, selected, updatedCompiled, rfl⟩

theorem assignment_source {σ : Type} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {lhs : Expr} {name : String} {path : List Bool}
    {value : Semantics.Value} (placed : Semantics.place? lhs = some (name, path))
    (assigned : Semantics.assignResult sourceEnvironment initial lhs value = .value final) :
    ∃ location old updated,
      Semantics.lookupLocation sourceEnvironment name = some location ∧
      initial.heap[location]? = some old ∧
      Semantics.updateProduct? path old value = some updated ∧
      final = {initial with heap := initial.heap.set location updated} := by
  simp only [Semantics.assignResult, placed] at assigned
  cases found : Semantics.lookupLocation sourceEnvironment name with
  | none => simp only [found] at assigned; contradiction
  | some location =>
      cases read : initial.heap[location]? with
      | none => simp only [found, read] at assigned; contradiction
      | some old =>
          cases updated : Semantics.updateProduct? path old value with
          | none => simp only [found, read, updated] at assigned; contradiction
          | some newValue =>
              have bound := (List.getElem?_eq_some_iff.mp read).1
              simp only [found, read, updated, Semantics.write?, bound,
                ↓reduceIte, Semantics.Result.value.injEq] at assigned
              exact ⟨location, old, newValue, rfl, read, updated, assigned.symm⟩

theorem assignment_core {result type : Core.Ty} {rhs updated : Core.Expr} {index : Nat}
    {mapping : Core.Renaming} {environment : Core.Environment}
    {initial middle final : Core.Store} {value old newValue : Core.Value} {location : Nat}
    (evaluated : Core.Evaluates environment initial (rhs.rename mapping)
      (.inRight .word value) middle)
    (found : environment[mapping index]? =
      some (.cellRef (Core.OptionalCell.cellType type) location))
    (read : middle.read? location = some (.inRight .unit old))
    (updatedEvaluated : Core.Evaluates (old :: value :: environment) middle
      (updated.rename mapping.lift.lift) newValue middle)
    (written : middle.write? location (.inRight .unit newValue) = some final) :
    Core.Evaluates environment initial
      ((Core.LanguageResult.bind (Core.LocalLoop.controlType result) rhs
        (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
          (Core.OptionalCell.read type (.var (index + 1)) (Core.Word.ofNatModulo 1))
          (.letE (.storeCell (.var (index + 2)) (.inRight .unit updated))
            (Core.LocalLoop.fallthrough result)))).rename mapping)
      (Core.LocalLoop.fallthroughValue result) final := by
  change Core.Evaluates environment initial
    (Core.LanguageResult.bind (Core.LocalLoop.controlType result) (rhs.rename mapping)
      (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
        (Core.OptionalCell.read type (.var (mapping index + 1)) (Core.Word.ofNatModulo 1))
        (.letE (.storeCell (.var (mapping index + 2)) (.inRight .unit (updated.rename mapping.lift.lift)))
          (Core.LocalLoop.fallthrough result)))) _ _
  apply Core.LanguageResult.bind_success _ evaluated
  have foundOne : (value :: environment)[mapping index + 1]? =
      some (.cellRef (Core.OptionalCell.cellType type) location) := found
  apply Core.LanguageResult.bind_success _
    (Core.OptionalCell.read_success _ (.var foundOne) read)
  have foundTwo : (old :: value :: environment)[mapping index + 2]? =
      some (.cellRef (Core.OptionalCell.cellType type) location) := found
  exact .letE (.storeCell (.var foundTwo) read (.inRight updatedEvaluated) written)
    (Core.LocalLoop.fallthrough_evaluates _ _ _)

/-- Every accepted local/product-path assignment preserves the source update.
The source and Core both select and read the root after the RHS effects. -/
theorem assignment {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {lhs rhs : Expr} (rightPreserves : NormalExprPreserves functions effects signatures external rhs)
    {sourceEnvironment : Semantics.Environment} {initial middle final : Semantics.State σ}
    {sourceValue : Semantics.Value} {span : Option Span}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment rhs initial
      (.value sourceValue) middle)
    (assigned : Semantics.assignResult sourceEnvironment middle lhs sourceValue = .value final)
    {fuel : Nat} {scope : Scope} {result : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue result) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  obtain ⟨right, name, path, binding, index, updated, rightCompiled, placed,
      looked, _, selected, updatedCompiled, rfl⟩ := assignment_components compiled
  obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleExternal⟩ :=
    rightPreserves sourceEvaluated rightCompiled environmentRelated heapRelated externalRelated
  obtain ⟨sourceLocation, sourceOld, sourceUpdated, found, read, updateSource, rfl⟩ :=
    assignment_source placed assigned
  obtain ⟨location, entry, _, targetFound⟩ :=
    (environmentRelated.extendWorld extension) name sourceLocation binding index found looked
  obtain ⟨oldValue, targetRead, oldRelated⟩ := middleHeap.read entry read
  have updatedRenamed : updateProduct path binding.type (.var 0) (.var 1) =
      .ok (updated.rename mapping.lift.lift) :=
    updateProduct_rename updatedCompiled mapping.lift.lift
  have oldEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
      (.var 0) oldValue middleStore := .var rfl
  have valueEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
      (.var 1) value middleStore := .var rfl
  obtain ⟨newValue, newRelated, updatedEvaluated⟩ :=
    updateProduct_evaluates updatedRenamed selected oldRelated valueRelated updateSource oldEvaluated valueEvaluated
  have written : middleStore.write? location (.inRight .unit newValue) =
      some (middleStore.set location (.inRight .unit newValue)) :=
    Core.Store.write?_eq_some_iff.mpr ⟨middleHeap.location_bound entry, rfl⟩
  exact ⟨extension, _, assignment_core evaluated targetFound targetRead updatedEvaluated written,
    middleHeap.write entry newRelated written, frame.write middleExternal middleHeap entry written⟩

end Solcore.Frontend.RustHull.StatementCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AssignmentValidity
/-! Accepted assignment paths and covered source locals exclude malformed
source updates. The source root is read after the RHS has finished. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence

private theorem place_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {lowered : Lowered} {name : String} {path : List Bool}
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (placed : place fuel expression = .ok (name, path)) :
    name.startsWith Effects.reservedPrefix = false := by
  induction fuel generalizing expression lowered name path with
  | zero => simp [place, fail] at placed
  | succ fuel ih =>
      cases expression with | mk type kind span =>
      cases kind <;> simp only [place] at placed
      all_goals try { simp [fail] at placed }
      case var localName =>
        cases placed
        simp only [lowerExpression] at compiled
        obtain ⟨expected, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        cases allowed : name.startsWith Effects.reservedPrefix
        · rfl
        · simp [allowed, fail, Bind.bind, Except.bind] at compiled
      case fst operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, _, _, operandCompiled, _, _⟩ :=
          lowerExpression_projection_components false compiled
        exact ih operandCompiled innerPlace
      case snd operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, _, _, operandCompiled, _, _⟩ :=
          lowerExpression_projection_components true compiled
        exact ih operandCompiled innerPlace

private theorem assignment_root_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {lhs rhs : Expr} {span : Option Span} {expression : Core.Expr}
    {name : String} {path : List Bool}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression)
    (placed : Semantics.place? lhs = some (name, path)) :
    name.startsWith Effects.reservedPrefix = false := by
  simp only [lowerStatement] at compiled
  obtain ⟨left, leftCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨right, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨⟨root, route⟩, placeCompiled, _⟩ := lower_bind_eq_ok.mp compiled
  have same := Option.some.inj ((place_correspondence placeCompiled).symm.trans placed)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact place_allowed leftCompiled placeCompiled

/-- A checked product path has a source update whenever the root has its
represented type. This also covers replacing the whole local at the empty path. -/
theorem updateProduct_exists {path : List Bool} {type selectedType : Core.Ty}
    {sourceOld sourceValue : Semantics.Value} {targetOld : Core.Value}
    (selected : fieldType path type = some selectedType)
    (related : ValueRel type sourceOld targetOld) :
    ∃ sourceUpdated, Semantics.updateProduct? path sourceOld sourceValue = some sourceUpdated := by
  induction path generalizing type sourceOld targetOld with
  | nil => exact ⟨sourceValue, rfl⟩
  | cons direction rest ih =>
      cases type <;> simp only [fieldType] at selected
      all_goals try contradiction
      case product leftType rightType =>
        cases related with
        | pair left right =>
            rename_i sourceLeft sourceRight targetLeft targetRight
            cases direction
            · obtain ⟨updated, found⟩ := ih selected left
              exact ⟨.pair updated sourceRight, by simp [Semantics.updateProduct?, found]⟩
            · obtain ⟨updated, found⟩ := ih selected right
              exact ⟨.pair sourceLeft updated, by simp [Semantics.updateProduct?, found]⟩

/-- Compilation checks the path, coverage supplies its source name, and HeapRel
supplies the initialized root and its type, so source assignment cannot be malformed. -/
theorem assignment_valid {σ : Type} {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {lhs rhs : Expr} {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression)
    {sourceEnvironment : Semantics.Environment} (covered : ScopeCoverage sourceEnvironment scope)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    {state : Semantics.State σ} {value : Semantics.Value}
    (locals : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heap : HeapRel world state.heap store) :
    ∃ finalState, Semantics.assignResult sourceEnvironment state lhs value = .value finalState := by
  obtain ⟨right, name, path, binding, index, updated, _, placed, looked, _, selected, _, _⟩ :=
    assignment_components compiled
  have allowed := assignment_root_allowed compiled placed
  obtain ⟨sourceLocation, found⟩ := covered name binding index allowed looked
  obtain ⟨location, entry, _, _⟩ := locals name sourceLocation binding index found looked
  obtain ⟨sourceOld, targetOld, read, _, related⟩ := heap.cell sourceLocation binding.type location entry
  obtain ⟨sourceUpdated, updated⟩ := updateProduct_exists (sourceValue := value) selected related
  have bound := (List.getElem?_eq_some_iff.mp read).1
  exact ⟨{state with heap := state.heap.set sourceLocation sourceUpdated}, by
    simp only [Semantics.assignResult, placed, found, read, updated, Semantics.write?, bound, ↓reduceIte]⟩

end Solcore.Frontend.RustHull.StatementCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ExpressionCorrespondence
/-! Operational correspondence for the expressions produced by the actual
Hull lowerer. Arbitrary variable renamings account for inserted Core binders
while retaining the caller's exact heap and stored function captures. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ExpressionCorrespondence

open Correspondence

theorem boolean_evaluates {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    {value : Bool} {expression : Core.Expr}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    (compiled : boolean type (.bool value) = .ok expression)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ∃ source target, Semantics.boolean? sourceType value = some source ∧
      ValueRel type source target ∧
      Core.Evaluates environment store (expression.rename mapping) target store := by
  obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape typeCompiled
  by_cases native : type = .bool
  · have same : shape = .bool := coreType_injective (targetShape.trans native)
    subst shape
    simp only [boolean, native, ↓reduceIte] at compiled
    cases compiled
    rw [native]
    exact ⟨.bool value, .bool value, by simp [Semantics.boolean?, sourceShape], .bool _, .bool⟩
  · by_cases sum : type = .sum .unit .unit
    · have same : shape = .sum .unit .unit := coreType_injective (targetShape.trans sum)
      subst shape
      simp only [boolean, sum, ↓reduceIte] at compiled
      cases compiled
      rw [sum]
      cases value with
      | false =>
          exact ⟨.inl .unit, .inLeft .unit .unit,
            by simp [Semantics.boolean?, sourceShape], .inl .unit, .ifFalse .bool (.inLeft .unit)⟩
      | true =>
          exact ⟨.inr .unit, .inRight .unit .unit,
            by simp [Semantics.boolean?, sourceShape], .inr .unit, .ifTrue .bool (.inRight .unit)⟩
    · simp [boolean, native, sum, fail] at compiled

theorem condition_evaluates {lowered : Lowered} {expression : Core.Expr}
    {source : Semantics.Value} {target : Core.Value} {value : Bool}
    (compiled : condition lowered = .ok expression)
    (related : ValueRel lowered.type source target)
    (truth : Semantics.condition? source = some value)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (lowered.expression.rename mapping)
      (.inRight .word target) final) :
    Core.Evaluates environment initial (expression.rename mapping)
      (.inRight .word (.bool value)) final := by
  by_cases native : lowered.type = .bool
  · simp only [condition, native, ↓reduceIte] at compiled
    cases compiled
    rw [native] at related
    cases related with
    | bool result =>
        simp only [Semantics.condition?, Option.some.injEq] at truth
        cases truth
        exact evaluated
  · by_cases sum : lowered.type = .sum .unit .unit
    · simp only [condition, sum, ↓reduceIte] at compiled
      cases compiled
      rw [sum] at related
      cases related with
      | inl payload =>
          cases payload
          simp only [Semantics.condition?, Option.some.injEq] at truth
          cases truth
          exact Core.LanguageResult.bind_success _ evaluated
            (.caseLeft (.var rfl) (.inRight .bool))
      | inr payload =>
          cases payload
          simp only [Semantics.condition?, Option.some.injEq] at truth
          cases truth
          exact Core.LanguageResult.bind_success _ evaluated
            (.caseRight (.var rfl) (.inRight .bool))
    · simp [condition, native, sum, fail] at compiled

theorem condition_failure {lowered : Lowered} {expression : Core.Expr} {reason : Core.Word}
    (compiled : condition lowered = .ok expression)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (lowered.expression.rename mapping)
      (.inLeft lowered.type (.word reason)) final) :
    Core.Evaluates environment initial (expression.rename mapping)
      (.inLeft .bool (.word reason)) final := by
  by_cases native : lowered.type = .bool
  · simp only [condition, native, ↓reduceIte] at compiled
    cases compiled
    simpa only [native] using evaluated
  · by_cases sum : lowered.type = .sum .unit .unit
    · simp only [condition, sum, ↓reduceIte] at compiled
      cases compiled
      exact Core.LanguageResult.bind_failure _ evaluated
    · simp [condition, native, sum, fail] at compiled

theorem bool {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {value : Bool} {lowered : Lowered}
    (kind : expression.kind = .bool value)
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ∃ target, ResultRel lowered.type (Semantics.booleanResult expression.ty value) target ∧
      Core.Evaluates environment store (lowered.expression.rename mapping) target store := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨type, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨code, boolCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      dsimp only [Bind.bind, Except.bind, Pure.pure] at compiled
      obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      obtain ⟨source, target, parsed, related, evaluated⟩ :=
        boolean_evaluates typeCompiled boolCompiled mapping environment store
      refine ⟨.inRight .word target, ?_, .inRight evaluated⟩
      simpa only [Semantics.booleanResult, parsed] using ResultRel.value related

theorem word {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {text : String} {lowered : Lowered}
    (kind : expression.kind = .word text)
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ∃ value, ResultRel lowered.type (Semantics.literalResult text) value ∧
      Core.Evaluates environment store (lowered.expression.rename mapping) value store := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨value, parsed, compiled⟩ := lower_bind_eq_ok.mp compiled
      dsimp only [Bind.bind, Except.bind, Pure.pure] at compiled
      obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      rw [Semantics.literalResult, parseWord_some_of_ok parsed]
      exact ⟨_, .value (.word value), .inRight .word⟩

theorem unit {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {lowered : Lowered}
    (kind : expression.kind = .unit)
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ResultRel lowered.type (.value .unit) (.inRight .word .unit) ∧
      Core.Evaluates environment store (lowered.expression.rename mapping)
        (.inRight .word .unit) store := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      dsimp only [Bind.bind, Except.bind, Pure.pure] at compiled
      obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      exact ⟨.value .unit, .inRight .unit⟩

theorem read {world : World} {sourceEnvironment : Semantics.Environment}
    {sourceHeap : Semantics.Heap} {scope : Scope} {mapping : Core.Renaming}
    {environment : Core.Environment} {store : Core.Store}
    (envRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world sourceHeap store)
    {name : String} {location : Nat} {sourceValue : Semantics.Value} {lowered : Lowered}
    (found : Semantics.lookupLocation sourceEnvironment name = some location)
    (read : sourceHeap[location]? = some sourceValue)
    (compiled : scope.read name = .ok lowered) :
    ∃ value, ValueRel lowered.type sourceValue value ∧
      Core.Evaluates environment store (lowered.expression.rename mapping)
        (.inRight .word value) store := by
  unfold Scope.read at compiled
  obtain ⟨⟨binding, index⟩, lookup, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨targetLocation, value, reference, variableLookup, initialized, related⟩ :=
    envRelated.read heapRelated found lookup read
  simp only [reference, ↓reduceIte] at returned
  cases returned
  refine ⟨value, related, ?_⟩
  exact Core.OptionalCell.read_success _ (.var variableLookup) initialized

end Solcore.Frontend.RustHull.ExpressionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.BuiltinCorrespondence
/-! Pure Hull builtin meaning through the actual builtin compiler. Argument
premises describe the emitted argument pack and its exact resulting store;
they can be supplied by expression-list preservation. External effects are not
assumed here. The raw Yul word operator executes only after that pack succeeds. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.BuiltinCorrespondence
open Correspondence

theorem primitiveName_meaning (name : String) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = Semantics.primitive? (primitiveName name) type arguments := by
  unfold primitiveName
  split <;> rfl

private theorem toOption_bind {α β ε : Type} (value : Except ε α) (next : α → Except ε β) :
    (value >>= next).toOption = value.toOption.bind (fun value => (next value).toOption) := by
  cases value <;> rfl

private theorem toOption_mapError {α ε δ : Type} (value : Except ε α) (map : ε → δ) :
    (value.mapError map).toOption = value.toOption := by
  cases value <;> rfl

theorem lowerBuiltin_primitiveName (scope : Scope) (name : String) (expected : Core.Ty)
    (arguments : List Lowered) :
    (lowerBuiltin scope name expected arguments).toOption =
      (lowerBuiltin scope (primitiveName name) expected arguments).toOption := by
  unfold primitiveName
  split <;> try rfl
  all_goals
    simp [lowerBuiltin, Effects.supports, Ambient.supports, AccountInspection.supports,
      primitiveName, toOption_bind, toOption_mapError]

inductive WordBinary where
  | add | sub | mul | udiv | umod | sdiv | smod | pow | signExtend
  | bitAnd | bitOr | bitXor | byteAt | shl | shr | sar
  deriving Repr, DecidableEq

def WordBinary.name : WordBinary → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .udiv => "div" | .umod => "mod"
  | .sdiv => "sdiv" | .smod => "smod" | .pow => "exp" | .signExtend => "signextend"
  | .bitAnd => "and" | .bitOr => "or" | .bitXor => "xor" | .byteAt => "byte"
  | .shl => "shl" | .shr => "shr" | .sar => "sar"

def WordBinary.eval : WordBinary → Core.Word → Core.Word → Core.Word
  | .add => Core.Word.add | .sub => Core.Word.sub | .mul => Core.Word.mul
  | .udiv => Core.Word.udiv | .umod => Core.Word.umod
  | .sdiv => Core.Word.sdiv | .smod => Core.Word.smod
  | .pow => Core.Word.pow | .signExtend => Core.Word.signExtend
  | .bitAnd => Core.Word.bitAnd | .bitOr => Core.Word.bitOr | .bitXor => Core.Word.bitXor
  | .byteAt => Core.Word.byteAt
  | .shl => fun distance value => Core.Word.shiftLeft value distance
  | .shr => fun distance value => Core.Word.shiftRight value distance
  | .sar => fun distance value => Core.Word.shiftArithmeticRight value distance

def WordBinary.operation : WordBinary → Core.BinaryOp
  | .add => .wordAdd | .sub => .wordSub | .mul => .wordMul
  | .udiv => .wordDiv | .umod => .wordMod | .sdiv => .wordSdiv | .smod => .wordSmod
  | .pow => .wordPow | .signExtend => .wordSignExtend
  | .bitAnd => .wordAnd | .bitOr => .wordOr | .bitXor => .wordXor | .byteAt => .wordByte
  | .shl => .wordShl | .shr => .wordShr | .sar => .wordSar

def WordBinary.body (operation : WordBinary) : Core.Expr :=
  match operation with
  | .shl | .shr | .sar => .binary operation.operation (.var 1) (.var 0)
  | _ => .binary operation.operation (.var 0) (.var 1)

/-- The actual pure-Yul adapter binds the right projection and then the left
projection. The enclosing Hull argument pack has already evaluated its inputs. -/
def WordBinary.code (operation : WordBinary) : Core.Expr :=
  .apply (.lambda .word .word
    (.apply (.lambda .word .word operation.body) (.first (.var 1)))) (.second (.var 0))

theorem WordBinary.lowered (operation : WordBinary) (scope : Scope) (left right : Core.Expr) :
    lowerBuiltin scope operation.name .word [⟨.word, left⟩, ⟨.word, right⟩] =
      .ok ⟨.word, Core.LanguageResult.bind .word
        (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
        (Core.LanguageResult.success operation.code)⟩ := by
  cases operation <;> rfl

theorem WordBinary.meaning (operation : WordBinary) (type : Ty) (left right : Core.Word) :
    Semantics.primitive? operation.name type [.word left, .word right] =
      some (.value (.word (operation.eval left right))) := by
  cases operation <;> rfl

theorem WordBinary.evaluates (operation : WordBinary) (left right : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.pair (.word left) (.word right) :: environment) store operation.code
      (.word (operation.eval left right)) store := by
  cases operation <;>
    exact .apply .lambda (.second (.var rfl))
      (.apply .lambda (.first (.var rfl)) (.binary (.var rfl) (.var rfl) rfl))

theorem WordBinary.renamed (operation : WordBinary) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

/-- All ordinary word binary builtins and their Hull aliases preserve their
independent arithmetic result and the exact argument-evaluation heap. -/
theorem wordBinary {name : String} (operation : WordBinary)
    (named : primitiveName name = operation.name)
    {scope : Scope} {left right : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name .word [⟨.word, left⟩, ⟨.word, right⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {leftValue rightValue : Core.Word}
    (arguments : Core.Evaluates environment initial
      ((packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression.rename mapping)
      (.inRight .word (.pair (.word leftValue) (.word rightValue))) final)
    (sourceType : Ty) :
    ∃ result target, Semantics.primitive? name sourceType [.word leftValue, .word rightValue] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  have normalized := lowerBuiltin_primitiveName scope name .word [⟨.word, left⟩, ⟨.word, right⟩]
  rw [compiled, named, operation.lowered] at normalized
  have same : lowered = ⟨.word, Core.LanguageResult.bind .word
      (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
      (Core.LanguageResult.success operation.code)⟩ := Option.some.inj normalized
  cases same
  refine ⟨.value (.word (operation.eval leftValue rightValue)),
    .inRight .word (.word (operation.eval leftValue rightValue)), ?_, .value (.word _), ?_⟩
  · rw [primitiveName_meaning, named]
    exact operation.meaning sourceType leftValue rightValue
  · change Core.Evaluates environment initial
      (Core.LanguageResult.bind .word
        ((packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression.rename mapping)
        (Core.LanguageResult.success (operation.code.rename mapping.lift))) _ final
    rw [operation.renamed]
    exact Core.LanguageResult.bind_success .word arguments
      (.inRight (operation.evaluates leftValue rightValue environment final))

inductive WordUnary where
  | bitNot | clz
  deriving Repr, DecidableEq

def WordUnary.name : WordUnary → String
  | .bitNot => "not" | .clz => "clz"

def WordUnary.eval : WordUnary → Core.Word → Core.Word
  | .bitNot => Core.Word.bitNot | .clz => Core.Word.clz

def WordUnary.operation : WordUnary → Core.UnaryOp
  | .bitNot => .wordNot | .clz => .wordClz

def WordUnary.code (operation : WordUnary) : Core.Expr :=
  .apply (.lambda .word .word (.unary operation.operation (.var 0))) (.var 0)

theorem WordUnary.lowered (operation : WordUnary) (scope : Scope) (argument : Core.Expr) :
    lowerBuiltin scope operation.name .word [⟨.word, argument⟩] =
      .ok ⟨.word, Core.LanguageResult.bind .word argument
        (Core.LanguageResult.success operation.code)⟩ := by
  cases operation <;> rfl

theorem WordUnary.meaning (operation : WordUnary) (type : Ty) (value : Core.Word) :
    Semantics.primitive? operation.name type [.word value] =
      some (.value (.word (operation.eval value))) := by
  cases operation <;> rfl

theorem WordUnary.evaluates (operation : WordUnary) (value : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.word value :: environment) store operation.code
      (.word (operation.eval value)) store := by
  cases operation <;> exact .apply .lambda (.var rfl) (.unary (.var rfl) rfl)

theorem WordUnary.renamed (operation : WordUnary) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

theorem wordUnary {name : String} (operation : WordUnary)
    (named : primitiveName name = operation.name)
    {scope : Scope} {argument : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name .word [⟨.word, argument⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {value : Core.Word}
    (evaluated : Core.Evaluates environment initial (argument.rename mapping)
      (.inRight .word (.word value)) final) (sourceType : Ty) :
    ∃ result target, Semantics.primitive? name sourceType [.word value] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  have normalized := lowerBuiltin_primitiveName scope name .word [⟨.word, argument⟩]
  rw [compiled, named, operation.lowered] at normalized
  have same : lowered = ⟨.word, Core.LanguageResult.bind .word argument
      (Core.LanguageResult.success operation.code)⟩ := Option.some.inj normalized
  cases same
  refine ⟨.value (.word (operation.eval value)), .inRight .word (.word (operation.eval value)),
    ?_, .value (.word _), ?_⟩
  · rw [primitiveName_meaning, named]
    exact operation.meaning sourceType value
  · change Core.Evaluates environment initial
      (Core.LanguageResult.bind .word (argument.rename mapping)
        (Core.LanguageResult.success (operation.code.rename mapping.lift))) _ final
    rw [operation.renamed]
    exact Core.LanguageResult.bind_success .word evaluated
      (.inRight (operation.evaluates value environment final))

/-- The Hull integer conversions are word-preserving in both specifications. -/
theorem conversion {name : String}
    (named : name = "wordToInteger" ∨ name = "wordFromInteger")
    {scope : Scope} {argument : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name .word [⟨.word, argument⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {value : Core.Word}
    (evaluated : Core.Evaluates environment initial (argument.rename mapping)
      (.inRight .word (.word value)) final) (sourceType : Ty) :
    Semantics.primitive? name sourceType [.word value] = some (.value (.word value)) ∧
      ResultRel lowered.type (.value (.word value)) (.inRight .word (.word value)) ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping)
        (.inRight .word (.word value)) final := by
  rcases named with rfl | rfl
  all_goals
    have same : ⟨.word, argument⟩ = lowered := Except.ok.inj compiled
    cases same
    exact ⟨rfl, .value (.word _), evaluated⟩

inductive WordTernary where
  | addMod | mulMod
  deriving Repr, DecidableEq

def WordTernary.name : WordTernary → String
  | .addMod => "addmod" | .mulMod => "mulmod"

def WordTernary.eval : WordTernary → Core.Word → Core.Word → Core.Word → Core.Word
  | .addMod => Core.Word.addMod | .mulMod => Core.Word.mulMod

def WordTernary.operation : WordTernary → Core.TernaryOp
  | .addMod => .wordAddMod | .mulMod => .wordMulMod

def WordTernary.code (operation : WordTernary) : Core.Expr :=
  .apply (.lambda .word .word
    (.apply (.lambda .word .word
      (.apply (.lambda .word .word (.ternary operation.operation (.var 0) (.var 1) (.var 2)))
        (.first (.var 2)))) (.first (.second (.var 1))))) (.second (.second (.var 0)))

theorem WordTernary.lowered (operation : WordTernary) (scope : Scope) (first second third : Core.Expr) :
    lowerBuiltin scope operation.name .word [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] =
      .ok ⟨.word, Core.LanguageResult.bind .word
        (packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression
        (Core.LanguageResult.success operation.code)⟩ := by
  cases operation <;> rfl

theorem WordTernary.meaning (operation : WordTernary) (type : Ty) (first second third : Core.Word) :
    Semantics.primitive? operation.name type [.word first, .word second, .word third] =
      some (.value (.word (operation.eval first second third))) := by
  cases operation <;> rfl

theorem WordTernary.evaluates (operation : WordTernary) (first second third : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.pair (.word first) (.pair (.word second) (.word third)) :: environment)
      store operation.code (.word (operation.eval first second third)) store := by
  cases operation <;>
    exact .apply .lambda (.second (.second (.var rfl)))
      (.apply .lambda (.first (.second (.var rfl)))
        (.apply .lambda (.first (.var rfl)) (.ternary (.var rfl) (.var rfl) (.var rfl) rfl)))

theorem WordTernary.renamed (operation : WordTernary) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

theorem wordTernary (operation : WordTernary)
    {scope : Scope} {first second third : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name .word
      [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {firstValue secondValue thirdValue : Core.Word}
    (arguments : Core.Evaluates environment initial
      ((packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression.rename mapping)
      (.inRight .word (.pair (.word firstValue) (.pair (.word secondValue) (.word thirdValue)))) final)
    (sourceType : Ty) :
    ∃ result target, Semantics.primitive? operation.name sourceType
        [.word firstValue, .word secondValue, .word thirdValue] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  rw [operation.lowered] at compiled
  cases compiled
  refine ⟨.value (.word (operation.eval firstValue secondValue thirdValue)),
    .inRight .word (.word (operation.eval firstValue secondValue thirdValue)),
    operation.meaning sourceType firstValue secondValue thirdValue, .value (.word _), ?_⟩
  change Core.Evaluates environment initial
    (Core.LanguageResult.bind .word
      ((packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression.rename mapping)
      (Core.LanguageResult.success (operation.code.rename mapping.lift))) _ final
  rw [operation.renamed]
  exact Core.LanguageResult.bind_success .word arguments
    (.inRight (operation.evaluates firstValue secondValue thirdValue environment final))

theorem pop {scope : Scope} {argument : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope "pop" .unit [⟨.word, argument⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {value : Core.Word}
    (evaluated : Core.Evaluates environment initial (argument.rename mapping)
      (.inRight .word (.word value)) final) (sourceType : Ty) :
    Semantics.primitive? "pop" sourceType [.word value] = some (.value .unit) ∧
      ResultRel lowered.type (.value .unit) (.inRight .word .unit) ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word .unit) final := by
  have same : ⟨.unit, Core.LanguageResult.bind .unit argument
      (Core.LanguageResult.success (.apply (.lambda .word .unit .unit) (.var 0)))⟩ = lowered :=
    Except.ok.inj compiled
  cases same
  exact ⟨rfl, .value .unit, Core.LanguageResult.bind_success .unit evaluated
    (.inRight (.apply .lambda (.var rfl) .unit))⟩

/-- Repackage an evaluated Core boolean according to the actual checked Hull
result type. This also covers Hull's sum-of-Unit boolean representation. -/
theorem booleanResult {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    {conditionCode expression : Core.Expr} {value : Bool}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    (compiled : boolean type conditionCode = .ok expression)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (conditionCode.rename mapping) (.bool value) final) :
    ∃ source target, Semantics.booleanResult sourceType value = .value source ∧
      ValueRel type source target ∧
      Core.Evaluates environment initial (expression.rename mapping) target final := by
  obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape typeCompiled
  by_cases native : type = .bool
  · have same : shape = .bool := coreType_injective (targetShape.trans native)
    subst shape
    simp only [boolean, native, ↓reduceIte] at compiled
    cases compiled
    rw [native]
    exact ⟨.bool value, .bool value,
      by simp [Semantics.booleanResult, Semantics.boolean?, sourceShape], .bool _, evaluated⟩
  · by_cases sum : type = .sum .unit .unit
    · have same : shape = .sum .unit .unit := coreType_injective (targetShape.trans sum)
      subst shape
      simp only [boolean, sum, ↓reduceIte] at compiled
      cases compiled
      rw [sum]
      cases value with
      | false => exact ⟨.inl .unit, .inLeft .unit .unit,
          by simp [Semantics.booleanResult, Semantics.boolean?, sourceShape],
          .inl .unit, .ifFalse evaluated (.inLeft .unit)⟩
      | true => exact ⟨.inr .unit, .inRight .unit .unit,
          by simp [Semantics.booleanResult, Semantics.boolean?, sourceShape],
          .inr .unit, .ifTrue evaluated (.inRight .unit)⟩
    · simp [boolean, native, sum, fail] at compiled

inductive WordComparison where
  | eq | lt | gt | slt | sgt
  deriving Repr, DecidableEq

def WordComparison.name : WordComparison → String
  | .eq => "eq" | .lt => "lt" | .gt => "gt" | .slt => "slt" | .sgt => "sgt"

def WordComparison.eval : WordComparison → Core.Word → Core.Word → Bool
  | .eq => (· == ·)
  | .lt => fun left right => left.val < right.val
  | .gt => fun left right => left.val > right.val
  | .slt => fun left right => Core.Word.signedGt right left
  | .sgt => Core.Word.signedGt

def WordComparison.body : WordComparison → Core.Expr
  | .eq => .binary .wordEq (.var 0) (.var 1)
  | .lt => .binary .wordGt (.var 1) (.var 0)
  | .gt => .binary .wordGt (.var 0) (.var 1)
  | .slt => .binary .wordSgt (.var 1) (.var 0)
  | .sgt => .binary .wordSgt (.var 0) (.var 1)

def WordComparison.wordCode (operation : WordComparison) : Core.Expr :=
  .apply (.lambda .word .word
    (.apply (.lambda .word .word
      (.ifE operation.body (.word (Core.Word.ofNatModulo 1)) (.word Core.Word.zero)))
      (.first (.var 1)))) (.second (.var 0))

def WordComparison.code (operation : WordComparison) : Core.Expr :=
  .unary .boolNot (.binary .wordEq operation.wordCode (.word Core.Word.zero))

theorem WordComparison.lowered (operation : WordComparison) (scope : Scope)
    (type : Core.Ty) (left right : Core.Expr) :
    lowerBuiltin scope operation.name type [⟨.word, left⟩, ⟨.word, right⟩] = (do
      let output ← boolean type operation.code
      pure ⟨type, Core.LanguageResult.bind type
        (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
        (Core.LanguageResult.success output)⟩) := by
  cases operation <;> rfl

theorem WordComparison.meaning (operation : WordComparison) (type : Ty) (left right : Core.Word) :
    Semantics.primitive? operation.name type [.word left, .word right] =
      some (Semantics.booleanResult type (operation.eval left right)) := by
  cases operation <;> rfl

theorem WordComparison.body_evaluates (operation : WordComparison) (left right : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.word left :: .word right :: environment) store operation.body
      (.bool (operation.eval left right)) store := by
  cases operation <;> exact .binary (.var rfl) (.var rfl) rfl

theorem WordComparison.evaluates (operation : WordComparison) (left right : Core.Word)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (.pair (.word left) (.word right) :: environment) store operation.code
      (.bool (operation.eval left right)) store := by
  have body := operation.body_evaluates left right
    (.pair (.word left) (.word right) :: environment) store
  cases truth : operation.eval left right with
  | false =>
      rw [truth] at body
      exact .unary (.binary
        (.apply .lambda (.second (.var rfl))
          (.apply .lambda (.first (.var rfl)) (.ifFalse body .word))) .word rfl) rfl
  | true =>
      rw [truth] at body
      exact .unary (.binary
        (.apply .lambda (.second (.var rfl))
          (.apply .lambda (.first (.var rfl)) (.ifTrue body .word))) .word rfl) rfl

theorem WordComparison.renamed (operation : WordComparison) (mapping : Core.Renaming) :
    operation.code.rename mapping.lift = operation.code := by
  cases operation <;> rfl

theorem wordComparison {name : String} (operation : WordComparison)
    (named : primitiveName name = operation.name)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {left right : Core.Expr} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type [⟨.word, left⟩, ⟨.word, right⟩] = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {leftValue rightValue : Core.Word}
    (arguments : Core.Evaluates environment initial
      ((packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression.rename mapping)
      (.inRight .word (.pair (.word leftValue) (.word rightValue))) final) :
    ∃ result target, Semantics.primitive? name sourceType [.word leftValue, .word rightValue] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  have normalized := lowerBuiltin_primitiveName scope name type [⟨.word, left⟩, ⟨.word, right⟩]
  rw [compiled, named, operation.lowered] at normalized
  cases boolCompiled : boolean type operation.code with
  | error error =>
      rw [boolCompiled] at normalized
      cases normalized
  | ok output =>
      rw [boolCompiled] at normalized
      have same : lowered = ⟨type, Core.LanguageResult.bind type
          (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
          (Core.LanguageResult.success output)⟩ := Option.some.inj normalized
      cases same
      have evaluated := operation.evaluates leftValue rightValue environment final
      rw [← operation.renamed mapping] at evaluated
      obtain ⟨source, target, meaning, related, evaluated⟩ := booleanResult typeCompiled boolCompiled evaluated
      refine ⟨.value source, .inRight .word target, ?_, .value related, ?_⟩
      · rw [primitiveName_meaning, named, operation.meaning, meaning]
      · exact Core.LanguageResult.bind_success type arguments (.inRight evaluated)

theorem boolLike_condition {type : Core.Ty} {source : Semantics.Value} {target : Core.Value}
    (supported : boolLike type = true) (related : ValueRel type source target) :
    ∃ truth, Semantics.condition? source = some truth := by
  have alternatives : type = .bool ∨ type = .sum .unit .unit := by
    cases type <;> simp_all [boolLike, BEq.beq, Core.instBEqTy.beq]
    rename_i left right
    cases left <;> cases right <;> simp_all [Core.instBEqTy.beq]
  rcases alternatives with native | sum
  · rw [native] at related
    cases related
    exact ⟨_, rfl⟩
  · rw [sum] at related
    cases related with
    | inl payload => cases payload; exact ⟨false, rfl⟩
    | inr payload => cases payload; exact ⟨true, rfl⟩

theorem iszero_lowered (scope : Scope) (type : Core.Ty) (argument : Lowered) :
    lowerBuiltin scope "iszero" type [argument] =
      (if boolLike argument.type then do
        let input ← condition argument
        let output ← boolean type (.unary .boolNot (.var 0))
        pure ⟨type, Core.LanguageResult.bind type input (Core.LanguageResult.success output)⟩
      else fail "Hull iszero expects one boolean value") := by
  rfl

theorem iszero {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {argument lowered : Lowered}
    (compiled : lowerBuiltin scope "iszero" type [argument] = .ok lowered)
    {source : Semantics.Value} {target : Core.Value}
    (related : ValueRel argument.type source target)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (argument.expression.rename mapping)
      (.inRight .word target) final) :
    ∃ result target, Semantics.primitive? "iszero" sourceType [source] = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final := by
  rw [iszero_lowered] at compiled
  split at compiled
  next supported =>
    obtain ⟨truth, sourceCondition⟩ := boolLike_condition supported related
    obtain ⟨input, inputCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨output, outputCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    have inputEvaluation := ExpressionCorrespondence.condition_evaluates inputCompiled related sourceCondition evaluated
    have negate : Core.Evaluates (.bool truth :: environment) final
        ((Core.Expr.unary .boolNot (.var 0)).rename mapping.lift) (.bool (!truth)) final :=
      .unary (.var rfl) rfl
    obtain ⟨sourceResult, targetResult, meaning, resultRelated, resultEvaluation⟩ :=
      booleanResult typeCompiled outputCompiled negate
    refine ⟨.value sourceResult, .inRight .word targetResult, ?_, .value resultRelated, ?_⟩
    · simp only [Semantics.primitive?, sourceCondition, meaning]
    · exact Core.LanguageResult.bind_success type inputEvaluation (.inRight resultEvaluation)
  next rejected => cases compiled

/-- A failed argument pack never executes the builtin body, including effect
builtins. The language error and the exact heap reached by the arguments are
preserved through the real compiler's wrapper. -/
theorem argument_failure {scope : Scope} {name : String} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    {reason : Core.Word}
    (evaluated : Core.Evaluates environment initial
      ((packArguments arguments).expression.rename mapping)
      (.inLeft (packArguments arguments).type (.word reason)) final) :
    Core.Evaluates environment initial (lowered.expression.rename mapping)
      (.inLeft lowered.type (.word reason)) final := by
  simp only [lowerBuiltin] at compiled
  split at compiled
  next effect =>
    obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    cases compiled
    exact Core.LanguageResult.bind_failure _ evaluated
  next pureOperation =>
    split at compiled
    next conversion =>
      split at compiled
      next arity =>
        obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        cases compiled
        exact evaluated
      next arity => cases compiled
    next ordinary =>
      split at compiled
      next zero =>
        split at compiled
        next supported =>
          obtain ⟨input, inputCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
          obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
          cases compiled
          exact Core.LanguageResult.bind_failure _
            (ExpressionCorrespondence.condition_failure inputCompiled evaluated)
        next unsupported => cases compiled
      next other =>
        obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        split at compiled
        next comparison =>
          obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
          cases compiled
          exact Core.LanguageResult.bind_failure _ evaluated
        next word =>
          obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
          cases checked
          cases compiled
          exact Core.LanguageResult.bind_failure _ evaluated

end Solcore.Frontend.RustHull.BuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LoopLoweringStructure
/-! Decompose the real Hull loop compiler. Initializers use its ordinary
statement-list path; a loop with no initializer allocates one Core self cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LoopLoweringStructure

/-- Actual compilation evidence for one loop, reused at every iteration. -/
structure Compiled (signatures : List Signature) (scope : Scope) (result : Core.Ty)
    (loops : Nat) (test : Expr) (post body : List Stmt) where
  fuel : Nat
  conditionCode : Lowered
  conditionCore : Core.Expr
  bodyCore : Core.Expr
  postCore : Core.Expr
  conditionCompiled : lowerExpression fuel signatures scope test = .ok conditionCode
  conditionConverted : condition conditionCode = .ok conditionCore
  bodyCompiled : lowerStatements fuel signatures scope result (loops + 1) body = .ok bodyCore
  postCompiled : lowerStatements fuel signatures scope result (loops + 1) post = .ok postCore

theorem empty_init_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {test : Expr} {post body : List Stmt}
    {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.forLoop [] test post body, span⟩ = .ok expression) :
    ∃ conditionCode conditionCore bodyCore postCore,
      lowerExpression fuel signatures scope test = .ok conditionCode ∧
      condition conditionCode = .ok conditionCore ∧
      lowerStatements fuel signatures scope result (loops + 1) body = .ok bodyCore ∧
      lowerStatements fuel signatures scope result (loops + 1) post = .ok postCore ∧
      expression = Core.LocalLoop.iterate result conditionCore bodyCore postCore (Core.Word.ofNatModulo 3) := by
  simp only [lowerStatement, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at compiled
  obtain ⟨conditionCode, conditionCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨conditionCore, converted, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨bodyCore, bodyCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨postCore, postCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  exact ⟨conditionCode, conditionCore, bodyCore, postCore,
    conditionCompiled, converted, bodyCompiled, postCompiled, rfl⟩

theorem nonempty_init {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {test : Expr} {init post body : List Stmt}
    {span : Option Span} {expression : Core.Expr} (nonempty : init ≠ [])
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.forLoop init test post body, span⟩ = .ok expression) :
    lowerStatements fuel signatures scope result loops
      (init ++ [⟨.forLoop [] test post body, span⟩]) = .ok expression := by
  cases init with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => simpa only [lowerStatement, List.isEmpty_cons, Bool.not_false, ↓reduceIte] using compiled

end Solcore.Frontend.RustHull.LoopLoweringStructure
end

section
-- leanmerge: from Solcore.Frontend.RustHull.PatternCorrespondence
/-! The actual pattern compiler preserves the independent source payload test.
Its supplied scrutinee is already evaluated by the match lowerer; the premise
below permits any expression that reads that value without changing the store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PatternCorrespondence
open Correspondence

inductive PatternResultRel (payload : Core.Ty) : Option Semantics.Value → Core.Value → Prop where
  | missed : PatternResultRel payload none (.inLeft payload .unit)
  | matched {source : Semantics.Value} {target : Core.Value}
      (related : ValueRel payload source target) :
      PatternResultRel payload (some source) (.inRight .unit target)

theorem index_preserves (shape : Semantics.Shape) {index : Nat}
    {source : Semantics.Value} {target : Core.Value}
    (related : ValueRel (coreType shape) source target)
    {payload : Core.Ty} {test : Core.Expr → Core.Expr}
    (compiled : testPattern.test index (coreType shape) = .ok (payload, test))
    {value : Core.Expr} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (supplied : Core.Evaluates environment store (value.rename mapping) target store) :
    ∃ result, PatternResultRel payload (Semantics.patternIndex? index shape source) result ∧
      Core.Evaluates environment store ((test value).rename mapping) result store := by
  induction shape generalizing index source target payload test value mapping environment with
  | sum left right _ ih =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, testPattern.test, ↓reduceIte] at compiled
        cases compiled
        cases related with
        | inl related =>
            exact ⟨_, .matched related, .caseLeft supplied (.inRight (.var rfl))⟩
        | inr related =>
            exact ⟨_, .missed, .caseRight supplied (.inLeft .unit)⟩
      · simp only [coreType, testPattern.test, zero, ↓reduceIte] at compiled
        obtain ⟨⟨nestedPayload, nestedTest⟩, nestedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        cases related with
        | inl related =>
            refine ⟨_, ?_, .caseLeft supplied (.inLeft .unit)⟩
            simpa only [Semantics.patternIndex?, zero, ↓reduceIte] using
              (PatternResultRel.missed (payload := nestedPayload))
        | inr related =>
            rename_i sourcePayload targetPayload
            have operand : Core.Evaluates (targetPayload :: environment) store
                ((Core.Expr.var 0).rename mapping.lift) targetPayload store := .var rfl
            obtain ⟨result, resultRelated, evaluated⟩ := ih related nestedCompiled operand
            exact ⟨result, by simpa only [Semantics.patternIndex?, zero, ↓reduceIte] using resultRelated,
              .caseRight supplied evaluated⟩
  | word | bool | unit | product =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, testPattern.test, ↓reduceIte] at compiled
        cases compiled
        exact ⟨_, .matched related, .inRight supplied⟩
      · simp [coreType, testPattern.test, zero, fail] at compiled

theorem test_preserves {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {source : Semantics.Value} {target : Core.Value}
    (related : ValueRel type source target)
    {pattern : PatKind} {payload : Core.Ty} {test : Core.Expr → Core.Expr}
    (compiled : testPattern type pattern = .ok (payload, test))
    {value : Core.Expr} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (supplied : Core.Evaluates environment store (value.rename mapping) target store) :
    ∃ result, PatternResultRel payload (Semantics.patternPayload? sourceType pattern source) result ∧
      Core.Evaluates environment store ((test value).rename mapping) result store := by
  cases pattern with
  | wildcard | var name =>
      cases compiled
      exact ⟨_, .matched related, .inRight supplied⟩
  | intLit text =>
      simp only [testPattern] at compiled
      obtain ⟨checked, matched, remaining⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      have same := expectType_eq_of_ok matched
      subst type
      obtain ⟨literal, parsed, returned⟩ := lower_bind_eq_ok.mp remaining
      cases returned
      cases related with
      | word word =>
          have compare : Core.Evaluates environment store
              ((Core.Expr.binary .wordEq value (.word literal)).rename mapping)
              (.bool (word == literal)) store := .binary supplied .word rfl
          cases equal : (word == literal) with
          | false =>
              refine ⟨_, ?_, .ifFalse (equal ▸ compare) (.inLeft .unit)⟩
              simpa only [Semantics.patternPayload?, parseWord_some_of_ok parsed, equal,
                Bool.false_eq_true, ↓reduceIte] using (PatternResultRel.missed (payload := .word))
          | true =>
              refine ⟨_, ?_, .ifTrue (equal ▸ compare) (.inRight supplied)⟩
              simpa only [Semantics.patternPayload?, parseWord_some_of_ok parsed, equal,
                ↓reduceIte] using (PatternResultRel.matched (ValueRel.word word))
  | con constructor =>
      cases constructor with
      | inl =>
          cases type <;> simp only [testPattern, fail] at compiled <;> try contradiction
          rename_i left right
          cases compiled
          cases related with
          | inl related => exact ⟨_, .matched related, .caseLeft supplied (.inRight (.var rfl))⟩
          | inr related => exact ⟨_, .missed, .caseRight supplied (.inLeft .unit)⟩
      | inr =>
          cases type <;> simp only [testPattern, fail] at compiled <;> try contradiction
          rename_i left right
          cases compiled
          cases related with
          | inl related => exact ⟨_, .missed, .caseLeft supplied (.inLeft .unit)⟩
          | inr related => exact ⟨_, .matched related, .caseRight supplied (.inRight (.var rfl))⟩
      | inK index =>
          obtain ⟨shape, sourceShape, typeShape⟩ := lowerType_shape typeCompiled
          subst type
          obtain ⟨result, resultRelated, evaluated⟩ := index_preserves shape related compiled supplied
          exact ⟨result, by simpa only [Semantics.patternPayload?, sourceShape,
            Bind.bind, Option.bind_some] using resultRelated, evaluated⟩

end Solcore.Frontend.RustHull.PatternCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.PureExpressionCorrespondence
/-! Independent source derivations instantiate the expression premise used by
the actual statement compiler. Literal and local-read cases require no assumed
correspondence for a function body or for an external operation. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.PureExpressionCorrespondence

open Correspondence StatementCorrespondence

theorem word {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (text : String) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .word text, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧ Semantics.Result.value sourceValue = Semantics.literalResult text := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, sourceResult⟩
  intro fuel scope lowered compiled world mapping environment store _ heap externalRelated
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.word rfl compiled mapping environment store
  rw [← sourceResult] at related
  cases related with
  | value payload => exact ⟨[], _, store, payload, evaluated, by simpa using heap, externalRelated⟩

theorem bool {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (value : Bool) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .bool value, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧ Semantics.Result.value sourceValue = Semantics.booleanResult type value := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, sourceResult⟩
  intro fuel scope lowered compiled world mapping environment store _ heap externalRelated
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.bool rfl compiled mapping environment store
  rw [← sourceResult] at related
  cases related with
  | value payload => exact ⟨[], _, store, payload, evaluated, by simpa using heap, externalRelated⟩

theorem unit {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .unit, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧ sourceValue = .unit := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, rfl⟩
  intro fuel scope lowered compiled world mapping environment store _ heap externalRelated
  obtain ⟨related, evaluated⟩ := ExpressionCorrespondence.unit rfl compiled mapping environment store
  cases related with
  | value payload => exact ⟨[], _, store, payload, evaluated, by simpa using heap, externalRelated⟩

end Solcore.Frontend.RustHull.PureExpressionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.StraightLineCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.StructuralExpressionCorrespondence
/-! Compositional correspondence for local reads and structured Hull values.
Every compiler premise refers to the actual lowering function. The source
premises are the independent evaluation rules, including their evaluation order.
-/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.PureExpressionCorrespondence

open Correspondence StatementCorrespondence

theorem read {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (name : String) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .var name, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧
      Semantics.readResult sourceEnvironment initial name = .value sourceValue := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, sourceResult⟩
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  unfold Semantics.readResult at sourceResult
  cases found : Semantics.lookupLocation sourceEnvironment name with
  | none => simp [found] at sourceResult
  | some location =>
      simp only [found] at sourceResult
      cases loaded : final.heap[location]? with
      | none => simp [loaded] at sourceResult
      | some value =>
          simp only [loaded, Semantics.Result.value.injEq] at sourceResult
          subst value
          obtain ⟨targetValue, related, evaluated⟩ :=
            variable_evaluates compiled environmentRelated heap found loaded
          exact ⟨[], targetValue, store, related, evaluated, by simpa using heap, externalRelated⟩

private theorem pair_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {left right : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment ⟨type, .pair left right, span⟩
      initial (.value sourceValue) final) :
    ∃ leftValue rightValue middle,
      sourceValue = .pair leftValue rightValue ∧
      Semantics.EvalExpr functions effects sourceEnvironment left initial (.value leftValue) middle ∧
      Semantics.EvalExpr functions effects sourceEnvironment right middle (.value rightValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherLeft otherRight leftValue rightResult kind first second
  cases rightResult with
  | fault reason => simp [Semantics.Result.map] at resultEq
  | value rightValue =>
      simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
      exact ⟨leftValue, rightValue, resultEq, middle, first, second⟩

theorem pair_rename (leftType rightType : Core.Ty) (left right : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalSequence.pair leftType rightType left right).rename mapping =
      Core.LocalSequence.pair leftType rightType (left.rename mapping) (right.rename mapping) := by
  simp [Core.LocalSequence.pair, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.Expr.rename, Core.Renaming.lift]

theorem pair {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {left right : Expr} (leftPreserves : NormalExprPreserves functions effects signatures external left)
    (rightPreserves : NormalExprPreserves functions effects signatures external right)
    (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .pair left right, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨leftValue, rightValue, middle, rfl, leftSource, rightSource⟩ := pair_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, rightCompiled, rfl⟩ :=
        lowerExpression_pair_components compiled
      obtain ⟨leftExtension, targetLeft, middleStore, leftRelated, leftEvaluation, middleHeap, middleExternal⟩ :=
        leftPreserves leftSource leftCompiled environmentRelated heap externalRelated
      have middleEnvironment := (environmentRelated.extendWorld leftExtension).prepend [targetLeft]
      obtain ⟨rightExtension, targetRight, finalStore, rightRelated, rightEvaluation, finalHeap, finalExternal⟩ :=
        rightPreserves rightSource rightCompiled middleEnvironment middleHeap middleExternal
      refine ⟨leftExtension ++ rightExtension, .pair targetLeft targetRight, finalStore,
        .pair leftRelated rightRelated, ?_, ?_, finalExternal⟩
      · have renamed : (rightCode.expression.rename mapping).weakenAt 0 =
            rightCode.expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        change Core.Evaluates environment store
          ((Core.LocalSequence.pair leftCode.type rightCode.type
            leftCode.expression rightCode.expression).rename mapping) _ _
        rw [pair_rename]
        apply Core.LocalSequence.pair_success _ _ leftEvaluation
        simpa [renamed] using rightEvaluation
      · simpa only [List.append_assoc] using finalHeap

private theorem projection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .snd operand else .fst operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.projectResult right value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value => exact ⟨value, evaluated, rfl⟩

theorem projection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {operand : Expr} (preserves : NormalExprPreserves functions effects signatures external operand)
    (right : Bool) (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, if right then .snd operand else .fst operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, projected⟩ := projection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_projection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated heap externalRelated
      rw [operandType] at related
      cases related with
      | pair leftRelated rightRelated =>
          cases right <;> simp only [Semantics.projectResult, Bool.false_eq_true, ↓reduceIte,
            Semantics.Result.value.injEq] at projected ⊢
          all_goals cases projected
          · exact ⟨extension, _, finalStore, leftRelated,
              Core.LanguageResult.bind_success _ evaluation (.inRight (.first (.var rfl))),
              finalHeap, finalExternal⟩
          · exact ⟨extension, _, finalStore, rightRelated,
              Core.LanguageResult.bind_success _ evaluation (.inRight (.second (.var rfl))),
              finalHeap, finalExternal⟩

private theorem injection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .inr target operand else .inl target operand, span⟩
      initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      sourceValue = (if right then .inr value else .inl value) := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherTarget otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value =>
        cases found : Semantics.shape otherTarget with
        | none => simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
        | some shape =>
            cases shape <;> simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
            exact ⟨value, evaluated, resultEq⟩

theorem injection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {operand : Expr} (preserves : NormalExprPreserves functions effects signatures external operand)
    (right : Bool) (type target : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, rfl⟩ := injection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, _, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_injection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated heap externalRelated
      rw [operandType] at related
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at related ⊢
      · exact ⟨extension, .inLeft rightType targetValue, finalStore, .inl related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl))),
          finalHeap, finalExternal⟩
      · exact ⟨extension, .inRight leftType targetValue, finalStore, .inr related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inRight (.var rfl))),
          finalHeap, finalExternal⟩

private theorem conditional_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {conditionExpr yes no : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial (.value sourceValue) final) :
    ∃ middle value truth,
      Semantics.EvalExpr functions effects sourceEnvironment conditionExpr initial (.value value) middle ∧
      Semantics.condition? value = some truth ∧
      Semantics.EvalExpr functions effects sourceEnvironment (if truth then yes else no)
        middle (.value sourceValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  case ifTrue => exact ⟨_, _, by assumption, Or.inr ⟨by assumption, by assumption⟩⟩
  case ifFalse => exact ⟨_, _, by assumption, Or.inl ⟨by assumption, by assumption⟩⟩

theorem choose_rename (type : Core.Ty) (conditionExpr yes no : Core.Expr) (mapping : Core.Renaming) :
    (Core.LocalControl.choose type conditionExpr yes no).rename mapping =
      Core.LocalControl.choose type (conditionExpr.rename mapping) (yes.rename mapping) (no.rename mapping) := by
  simp [Core.LocalControl.choose, Core.LanguageResult.bind, Core.Expr.rename, Core.Renaming.lift]

theorem conditional {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {conditionExpr yes no : Expr}
    (conditionPreserves : NormalExprPreserves functions effects signatures external conditionExpr)
    (yesPreserves : NormalExprPreserves functions effects signatures external yes)
    (noPreserves : NormalExprPreserves functions effects signatures external no)
    (type target : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, .ifThen target conditionExpr yes no, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨middle, conditionValue, truth, conditionSource, tested, branchSource⟩ := conditional_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        yesCompiled, noCompiled, yesType, noType, expressionEqual⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨conditionExtension, targetCondition, middleStore, conditionRelated,
        conditionEvaluation, middleHeap, middleExternal⟩ :=
        conditionPreserves conditionSource conditionCompiled environmentRelated heap externalRelated
      have testEvaluation := ExpressionCorrespondence.condition_evaluates
        testCompiled conditionRelated tested conditionEvaluation
      have middleEnvironment :=
        (environmentRelated.extendWorld conditionExtension).prepend [.bool truth]
      have branchPreserves : NormalExprPreserves functions effects signatures external
          (if truth then yes else no) := by cases truth <;> assumption
      have branchCompiled : lowerExpression fuel signatures scope (if truth then yes else no) =
          .ok (if truth then yesCode else noCode) := by cases truth <;> assumption
      obtain ⟨branchExtension, targetValue, finalStore, related, branchEvaluation, finalHeap, finalExternal⟩ :=
        branchPreserves branchSource branchCompiled middleEnvironment middleHeap middleExternal
      refine ⟨conditionExtension ++ branchExtension, targetValue, finalStore, ?_, ?_, ?_, finalExternal⟩
      · cases truth <;> simpa only [Bool.false_eq_true, ↓reduceIte, yesType, noType] using related
      · have renamed (expression : Core.Expr) : (expression.rename mapping).weakenAt 0 =
            expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        rw [expressionEqual, choose_rename]
        cases truth with
        | false =>
            apply Core.LocalControl.choose_false _ testEvaluation
            simpa [renamed] using branchEvaluation
        | true =>
            apply Core.LocalControl.choose_true _ testEvaluation
            simpa [renamed] using branchEvaluation
      · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.PureExpressionCorrespondence
end
