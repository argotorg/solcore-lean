import Solcore.Test.SourceCoreMixedWhileSource

/-! The loop executes twice when enabled and zero times otherwise. Every write
updates one real ordinary Source cell; the earlier descriptor stays in the prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedWhile
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def phaseHeap (base : Dynamic.Heap) (active first : Bool) (counter : Word) : Dynamic.Heap :=
  ⟨base.cells ++ [⟨.bool,some (.bool active),none⟩,
    ⟨.bool,some (.bool first),none⟩,⟨.word,some (.word counter),none⟩]⟩
def phaseEnvironment {source : TypedSource} (shape : Shape source)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) : Dynamic.Environment :=
  (shape.counter.id,⟨base.cells.length + 2⟩) :: (shape.first.id,⟨base.cells.length + 1⟩) ::
    (shape.active.id,⟨base.cells.length⟩) :: environment

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
    Dynamic.Heap.Reads (phaseHeap base active first counter) ⟨base.cells.length⟩ ⟨.bool,some (.bool active),none⟩ := by
  exact .intro (by simpa only [phaseHeap,Nat.add_zero] using cell_append base.cells (Dynamic.Heap.CellAt.head (cells := [⟨.bool,some (.bool first),none⟩,⟨.word,some (.word counter),none⟩])))
theorem phaseHeap.first (base : Dynamic.Heap) (active first : Bool) (counter : Word) :
    Dynamic.Heap.Reads (phaseHeap base active first counter) ⟨base.cells.length+1⟩ ⟨.bool,some (.bool first),none⟩ := by
  exact .intro (cell_append base.cells (.tail .head))
theorem phaseHeap.counter (base : Dynamic.Heap) (active first : Bool) (counter : Word) :
    Dynamic.Heap.Reads (phaseHeap base active first counter) ⟨base.cells.length+2⟩ ⟨.word,some (.word counter),none⟩ := by
  exact .intro (cell_append base.cells (.tail (.tail .head)))

theorem phaseHeap.write_active (base : Dynamic.Heap) (active first next : Bool) (counter : Word) :
    Dynamic.Heap.Writes (phaseHeap base active first counter) ⟨base.cells.length⟩ (some (.bool next))
      (phaseHeap base next first counter) := by
  exact .intro (phaseHeap.active base active first counter) (by simpa only [phaseHeap,Nat.add_zero] using write_append base.cells (Dynamic.Heap.CellsWrite.head))
theorem phaseHeap.write_first (base : Dynamic.Heap) (active first next : Bool) (counter : Word) :
    Dynamic.Heap.Writes (phaseHeap base active first counter) ⟨base.cells.length+1⟩ (some (.bool next))
      (phaseHeap base active next counter) := by
  exact .intro (phaseHeap.first base active first counter) (write_append base.cells (.tail .head))
theorem phaseHeap.write_counter (base : Dynamic.Heap) (active first : Bool) (counter next : Word) :
    Dynamic.Heap.Writes (phaseHeap base active first counter) ⟨base.cells.length+2⟩ (some (.word next))
      (phaseHeap base active first next) := by
  exact .intro (phaseHeap.counter base active first counter) (write_append base.cells (.tail (.tail .head)))

theorem Shape.active_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (active first : Bool) (counter : Word) :
    StoredValue shape.active (phaseEnvironment shape base environment) (phaseHeap base active first counter) (.bool active) :=
  ⟨_,_,.tail shape.counterActive (.tail shape.firstActive .head),phaseHeap.active base active first counter,rfl,rfl⟩
theorem Shape.first_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (active first : Bool) (counter : Word) :
    StoredValue shape.first (phaseEnvironment shape base environment) (phaseHeap base active first counter) (.bool first) :=
  ⟨_,_,.tail shape.counterFirst .head,phaseHeap.first base active first counter,rfl,rfl⟩
theorem Shape.counter_stored {source : TypedSource} (shape : Shape source) (base : Dynamic.Heap)
    (environment : Dynamic.Environment) (active first : Bool) (counter : Word) :
    StoredValue shape.counter (phaseEnvironment shape base environment) (phaseHeap base active first counter) (.word counter) :=
  ⟨_,_,.head,phaseHeap.counter base active first counter,rfl,rfl⟩

private theorem bare_assign {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {binder : Resolved.LocalId} {type : TypeSystem.Ty} {operator : Syntax.ValueAssignOp}
    {rhs : ExpressionId} (site : StatementAt source (.assignValue ⟨⟨binder,[],type⟩,[]⟩ operator rhs))
    {location : Dynamic.Location} {old right updated : Dynamic.Value}
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location ⟨type,some old,none⟩)
    (evaluates : Dynamic.ExpressionEvaluates program context evidence source environment before rhs right before)
    (operation : Dynamic.AssignmentValueApplies operator (some old) right updated)
    (write : Dynamic.Heap.Writes before location (some updated) after) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id context
      (.fallthrough environment) after := by
  apply Dynamic.StatementExecutes.assignValue (updatedRoot := updated) (lookupStatement?_sound site.found) site.formEq
  refine .intro (.intro lookup read .nil read .initialized .nil) evaluates ?_
  exact .intro read rfl .initialized (.leaf operation) write

private theorem Shape.increment_trace {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (active first : Bool) (counter : Word)
    (unique : NodeOccurrencesUnique source) (oneTyped : ExpressionHasType source context shape.one.node.id .word) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base active first counter) shape.increment.node.id context
      (.fallthrough (phaseEnvironment shape base environment))
      (phaseHeap base active first (counter.add (Word.ofNatModulo 1))) := by
  have literal := shape.one.evaluates (program := program) evidence (phaseEnvironment shape base environment)
    (phaseHeap base active first counter) unique oneTyped
  rw [shape.oneValue] at literal
  exact bare_assign shape.increment .head (phaseHeap.counter base active first counter) literal
    (.add (.wordAdd _ _)) (phaseHeap.write_counter base active first counter _)

private theorem Shape.branch_first {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (counter : Word) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base true true counter) shape.branch.node.id context
      (.fallthrough (phaseEnvironment shape base environment)) (phaseHeap base true false counter) := by
  have assigned := bare_assign (program := program) (context := context) (evidence := evidence)
    (environment := phaseEnvironment shape base environment)
    shape.firstWrite (.tail shape.counterFirst .head) (phaseHeap.first base true true counter)
    (boolean_value shape.firstFalse) (.equal _ _) (phaseHeap.write_first base true true false counter)
  exact .ifTrue (lookupStatement?_sound shape.branch.found) shape.branch.formEq
    (read_value shape.phaseRead (shape.first_stored base environment true true counter)) (.cons assigned .nil)

private theorem Shape.branch_second {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (counter : Word) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base true false counter) shape.branch.node.id context
      (.fallthrough (phaseEnvironment shape base environment)) (phaseHeap base false false counter) := by
  have assigned := bare_assign (program := program) (context := context) (evidence := evidence)
    (environment := phaseEnvironment shape base environment)
    shape.activeWrite (.tail shape.counterActive (.tail shape.firstActive .head)) (phaseHeap.active base true false counter)
    (boolean_value shape.activeFalse) (.equal _ _) (phaseHeap.write_active base true false false counter)
  exact .ifFalseWithElse (lookupStatement?_sound shape.branch.found) shape.branch.formEq
    (read_value shape.phaseRead (shape.first_stored base environment true false counter)) (.cons assigned .nil)

def loopCounter (flag : Bool) : Word := Word.ofNatModulo (if flag then 2 else 0)

theorem Shape.loop_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context shape.loop.node.id final facts) (flag : Bool) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base flag true (Word.ofNatModulo 0)) shape.loop.node.id final
      (.fallthrough (phaseEnvironment shape base environment)) (phaseHeap base false (!flag) (loopCounter flag)) := by
  have form := form_at unique shape.loop.found typed
  rw [shape.loop.formEq] at form
  cases form with
  | whileLoop _ body =>
    obtain ⟨_,_,_,incrementTyped,_⟩ := head_tail body
    have incrementForm := form_at unique shape.increment.found incrementTyped
    rw [shape.increment.formEq] at incrementForm
    cases incrementForm with
    | assignValue assigned =>
      have oneTyped : ExpressionHasType source context shape.one.node.id .word := by
        cases assigned with | wordCompound _ _ value _ => exact value
      apply Dynamic.StatementExecutes.whileLoop (finalContext := context)
        (outcome := .fallthrough (phaseEnvironment shape base environment))
        (lookupStatement?_sound shape.loop.found) shape.loop.formEq
      cases flag with
      | false => exact .done (read_value shape.guardRead (shape.active_stored base environment false true _))
      | true =>
        have first := shape.increment_trace (program := program) evidence base environment true true (Word.ofNatModulo 0) unique oneTyped
        have second := shape.increment_trace (program := program) evidence base environment true false (Word.ofNatModulo 1) unique oneTyped
        have add0 : (Word.ofNatModulo 0).add (Word.ofNatModulo 1) = Word.ofNatModulo 1 := by decide
        have add1 : (Word.ofNatModulo 1).add (Word.ofNatModulo 1) = Word.ofNatModulo 2 := by decide
        rw [add0] at first
        rw [add1] at second
        exact .nextFallthrough (read_value shape.guardRead (shape.active_stored base environment true true _))
          (.cons first (.cons (shape.branch_first context evidence base environment _) .nil))
          (.nextFallthrough (read_value shape.guardRead (shape.active_stored base environment true false _))
            (.cons second (.cons (shape.branch_second context evidence base environment _) .nil))
            (.done (read_value shape.guardRead (shape.active_stored base environment false false _))))

end Tests.SourceCoreMixedWhile
