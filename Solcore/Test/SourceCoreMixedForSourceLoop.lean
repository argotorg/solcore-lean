import Solcore.Test.SourceCoreMixedForSource

/-! Actual header allocation, continue/post, and break execution preserve the
earlier generalized descriptor. The header environment is restored on exit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedFor
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def outerHeap (base : Dynamic.Heap) (first : Bool) (counter : Word) : Dynamic.Heap :=
  ⟨base.cells ++ [⟨.bool,some (.bool first),none⟩,⟨.word,some (.word counter),none⟩]⟩
def phaseHeap (base : Dynamic.Heap) (active first : Bool) (counter : Word) : Dynamic.Heap :=
  ⟨base.cells ++ [⟨.bool,some (.bool first),none⟩,
    ⟨.word,some (.word counter),none⟩,⟨.bool,some (.bool active),none⟩]⟩
def outerEnvironment {source : TypedSource} (shape : Shape source)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) : Dynamic.Environment :=
  (shape.counter.id,⟨base.cells.length + 1⟩) :: (shape.first.id,⟨base.cells.length⟩) :: environment
def phaseEnvironment {source : TypedSource} (shape : Shape source)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) : Dynamic.Environment :=
  (shape.active.id,⟨base.cells.length + 2⟩) :: outerEnvironment shape base environment

theorem outerHeap.prefix (base : Dynamic.Heap) (first : Bool) (counter : Word) :
    HeapAppends base (outerHeap base first counter) := ⟨_,rfl⟩
theorem phaseHeap.prefix (base : Dynamic.Heap) (active first : Bool) (counter : Word) :
    HeapAppends base (phaseHeap base active first counter) := ⟨_,rfl⟩

private theorem cell_append (earlier : List Dynamic.Cell) {tail : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (read : Dynamic.Heap.CellAt tail index cell) :
    Dynamic.Heap.CellAt (earlier ++ tail) (earlier.length + index) cell := by
  induction earlier with
  | nil => simpa using read
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellAt.tail ih

private theorem write_append (earlier : List Dynamic.Cell) {before after : List Dynamic.Cell}
    {index : Nat} {cell : Dynamic.Cell} (write : Dynamic.Heap.CellsWrite before index cell after) :
    Dynamic.Heap.CellsWrite (earlier ++ before) (earlier.length + index) cell (earlier ++ after) := by
  induction earlier with
  | nil => simpa using write
  | cons head rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Dynamic.Heap.CellsWrite.tail ih

theorem phaseHeap.active (base : Dynamic.Heap) (active first : Bool) (counter : Word) :
    Dynamic.Heap.Reads (phaseHeap base active first counter) ⟨base.cells.length+2⟩ ⟨.bool,some (.bool active),none⟩ :=
  .intro (cell_append base.cells (.tail (.tail .head)))
theorem phaseHeap.first (base : Dynamic.Heap) (active first : Bool) (counter : Word) :
    Dynamic.Heap.Reads (phaseHeap base active first counter) ⟨base.cells.length⟩ ⟨.bool,some (.bool first),none⟩ := by
  exact .intro (by simpa only [phaseHeap,Nat.add_zero] using cell_append base.cells (Dynamic.Heap.CellAt.head (cells := [⟨.word,some (.word counter),none⟩,⟨.bool,some (.bool active),none⟩])))
theorem phaseHeap.counter (base : Dynamic.Heap) (active first : Bool) (counter : Word) :
    Dynamic.Heap.Reads (phaseHeap base active first counter) ⟨base.cells.length+1⟩ ⟨.word,some (.word counter),none⟩ :=
  .intro (cell_append base.cells (.tail .head))
theorem phaseHeap.write_first (base : Dynamic.Heap) (active first next : Bool) (counter : Word) :
    Dynamic.Heap.Writes (phaseHeap base active first counter) ⟨base.cells.length⟩ (some (.bool next))
      (phaseHeap base active next counter) := by
  exact .intro (phaseHeap.first base active first counter) (by simpa only [phaseHeap,Nat.add_zero] using write_append base.cells (Dynamic.Heap.CellsWrite.head))
theorem phaseHeap.write_counter (base : Dynamic.Heap) (active first : Bool) (counter next : Word) :
    Dynamic.Heap.Writes (phaseHeap base active first counter) ⟨base.cells.length+1⟩ (some (.word next))
      (phaseHeap base active first next) :=
  .intro (phaseHeap.counter base active first counter) (write_append base.cells (.tail .head))

theorem Shape.active_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (active first : Bool) (counter : Word) :
    StoredValue shape.active (phaseEnvironment shape base environment) (phaseHeap base active first counter) (.bool active) :=
  ⟨_,_,.head,phaseHeap.active base active first counter,rfl,rfl⟩
theorem Shape.first_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (active first : Bool) (counter : Word) :
    StoredValue shape.first (phaseEnvironment shape base environment) (phaseHeap base active first counter) (.bool first) :=
  ⟨_,_,.tail (Ne.symm shape.firstActive) (.tail shape.counterFirst .head),phaseHeap.first base active first counter,rfl,rfl⟩
theorem Shape.counter_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (active first : Bool) (counter : Word) :
    StoredValue shape.counter (outerEnvironment shape base environment) (phaseHeap base active first counter) (.word counter) :=
  ⟨_,_,.head,phaseHeap.counter base active first counter,rfl,rfl⟩

private theorem bare_assign {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {binder : Resolved.LocalId} {type : TypeSystem.Ty} {operator : Syntax.ValueAssignOp}
    {rhs : ExpressionId} {location : Dynamic.Location} {old right updated : Dynamic.Value}
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location ⟨type,some old,none⟩)
    (evaluates : Dynamic.ExpressionEvaluates program context evidence source environment before rhs right before)
    (operation : Dynamic.AssignmentValueApplies operator (some old) right updated)
    (write : Dynamic.Heap.Writes before location (some updated) after) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before ⟨binder,[],type⟩ rhs updated after :=
  .intro (.intro lookup read .nil read .initialized .nil) evaluates
    (.intro read rfl .initialized (.leaf operation) write)

private theorem Shape.post_trace {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (counter : Word)
    (unique : NodeOccurrencesUnique source) (oneTyped : ExpressionHasType source context shape.one.node.id .word) :
    Dynamic.ForItemsExecute program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base true false counter)
      [.assignValue ⟨⟨shape.counter.id,[],.word⟩,[]⟩ .add shape.one.node.id] context
      (phaseEnvironment shape base environment) (phaseHeap base true false (counter.add (Word.ofNatModulo 1))) := by
  have literal := shape.one.evaluates (program := program) evidence (phaseEnvironment shape base environment)
    (phaseHeap base true false counter) unique oneTyped
  rw [shape.oneValue] at literal
  exact .cons (.assignValue (bare_assign (.tail (Ne.symm shape.counterActive) .head)
    (phaseHeap.counter base true false counter) literal (.add (.wordAdd _ _))
    (phaseHeap.write_counter base true false counter _))) .nil

private theorem Shape.branch_first {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (counter : Word) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base true true counter) shape.branch.node.id context
      (.continuing (phaseEnvironment shape base environment)) (phaseHeap base true false counter) := by
  have assigned := Dynamic.StatementExecutes.assignValue (program := program) (context := context)
    (evidence := evidence) (environment := phaseEnvironment shape base environment)
    (lookupStatement?_sound shape.firstWrite.found) shape.firstWrite.formEq
    (bare_assign (.tail (Ne.symm shape.firstActive) (.tail shape.counterFirst .head))
      (phaseHeap.first base true true counter) (boolean_value shape.firstFalse)
      (.equal _ _) (phaseHeap.write_first base true true false counter))
  exact .ifTrue (lookupStatement?_sound shape.branch.found) shape.branch.formEq
    (read_value shape.phaseRead (shape.first_stored base environment true true counter))
    (.cons assigned (.terminal (.continueStmt (lookupStatement?_sound shape.continuing.found) shape.continuing.formEq) (.continuing _)))

private theorem Shape.branch_second {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (counter : Word) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base true false counter) shape.branch.node.id context
      (.breaking (phaseEnvironment shape base environment)) (phaseHeap base true false counter) :=
  .ifFalseWithElse (lookupStatement?_sound shape.branch.found) shape.branch.formEq
    (read_value shape.phaseRead (shape.first_stored base environment true false counter))
    (.terminal (.breakStmt (lookupStatement?_sound shape.breaking.found) shape.breaking.formEq) (.breaking _))

def loopCounter (flag : Bool) : Word := Word.ofNatModulo (if flag then 1 else 0)

theorem Shape.loop_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context shape.loop.node.id final facts) (flag : Bool)
    (flagStored : StoredValue shape.flag (outerEnvironment shape base environment)
      (outerHeap base true (Word.ofNatModulo 0)) (.bool flag)) :
    Dynamic.StatementExecutes program context evidence source (outerEnvironment shape base environment)
      (outerHeap base true (Word.ofNatModulo 0)) shape.loop.node.id final
      (.fallthrough (outerEnvironment shape base environment)) (phaseHeap base flag (!flag) (loopCounter flag)) := by
  have form := form_at unique shape.loop.found typed
  rw [shape.loop.formEq] at form
  cases form with
  | @forLoop _ _ _ _ loopContext _ _ _ initial _ _ post =>
    cases initial with
    | cons initialized tail =>
      cases tail
      cases initialized with
      | letInitialized _ mono _ extended =>
        cases post with
        | cons assigned tail =>
          cases assigned with
          | assignValue assigned =>
            have oneTyped : ExpressionHasType source loopContext shape.one.node.id .word := by
              cases assigned with | wordCompound _ _ value _ => exact value
            have allocated : Dynamic.Heap.Allocates (outerHeap base true (Word.ofNatModulo 0))
                shape.active.scheme.body (some (.bool flag)) ⟨base.cells.length+2⟩
                (phaseHeap base flag true (Word.ofNatModulo 0)) := by
              rw [shape.activeScheme]
              simpa only [outerHeap,phaseHeap,TypeSystem.Scheme.mono,List.length_append,List.length_cons,
                List.length_nil,List.append_assoc,List.cons_append,List.nil_append] using
                (Dynamic.Heap.Allocates.append (heap := outerHeap base true (Word.ofNatModulo 0))
                  (type := .bool) (value := some (.bool flag)))
            apply Dynamic.StatementExecutes.forLoop (program := program) (evidence := evidence)
              (loopFinalContext := loopContext) (outcome := .fallthrough (phaseEnvironment shape base environment))
              (lookupStatement?_sound shape.loop.found) shape.loop.formEq
              (.cons (.letInitialized (read_value shape.inputRead flagStored) mono extended allocated) .nil)
            cases flag with
            | false => exact .done (read_value shape.guardRead (shape.active_stored base environment false true _))
            | true =>
              have postTrace := shape.post_trace (program := program) evidence base environment (Word.ofNatModulo 0) unique oneTyped
              have add0 : (Word.ofNatModulo 0).add (Word.ofNatModulo 1) = Word.ofNatModulo 1 := by decide
              rw [add0] at postTrace
              exact .nextContinue (read_value shape.guardRead (shape.active_stored base environment true true _))
                (.terminal (shape.branch_first _ evidence base environment _) (.continuing _)) postTrace
                (.breaks (read_value shape.guardRead (shape.active_stored base environment true false _))
                  (.terminal (shape.branch_second _ evidence base environment _) (.breaking _)))
      | letInitializedGeneralized impossible _ _ _ _ =>
        exact (impossible (by rw [shape.activeScheme]; rfl)).elim

end Tests.SourceCoreMixedFor
