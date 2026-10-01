import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation

/-! Finite, table-derived ordinary Core dispatch for indexed ancestry.
Generated expressions compare only native scalar IDs. The owned preparation
table retains all source metadata and read/application recipes; runtime
dispatch neither traverses source IR nor reconstructs a recursive frame.

An invalid carrier is a failed administrative lookup, not authenticated source
history and not a language failure. The execution adapter must reject it.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedDispatch
open Core SourceCoreCallableIndexedFrames
abbrev Frame := SourceCoreCallableIndexedFrames.Frame
abbrev Table := SourceCoreCallableAncestryPairedCache.Table
abbrev State := SourceCoreCallableAncestryPairedCache.State
abbrev LambdaEdge := SourceCoreCallableAncestryPairedCache.LambdaEdge
abbrev ViewEdge := SourceCoreCallableAncestryPairedCache.ViewEdge
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared

def lookup? (table : Table) : Frame → Option (Option State)
  | .empty => some none
  | .state index => do
      let position ← naturalIndex? index
      let state ← table.stateAt? position
      pure (some state)
  | .view .. | .invalid => none

def checkedState (table : Table) (position : Nat) : Frame :=
  if (table.stateAt? position).isSome then .state (Int.ofNat position) else .invalid

def namedFrame (table : Table) (origin : Word) : Frame :=
  match table.namedAt? origin with
  | none => .invalid
  | some position => checkedState table position

def plainRows (table : Table) (origin : Word) (lexical : Int) : List LambdaEdge → Frame
  | [] => .invalid
  | edge :: rest =>
    if edge.origin = origin ∧ lexical = Int.ofNat edge.state then checkedState table edge.state
    else plainRows table origin lexical rest

def viewRows (table : Table) (origin id : Word) (caller lexical : Int) : List ViewEdge → Frame
  | [] => .invalid
  | edge :: rest =>
    if edge.target = origin ∧ edge.view = id ∧ caller = Int.ofNat edge.caller ∧ lexical = Int.ofNat edge.lexical then
      checkedState table edge.destination
    else viewRows table origin id caller lexical rest

def selectedFrame (table : Table) (origin : Word) (lexical current : Frame) : Frame :=
  match lexical with
  | .state index =>
    match current with
    | .view id target caller =>
      if target = origin then viewRows table origin id caller index table.views
      else plainRows table origin index table.lambdas
    | _ => plainRows table origin index table.lambdas
  | _ => .invalid

def literal (layout : Layout) : Frame → Expr
  | .empty => empty layout
  | .state index => state layout (.integer index)
  | .view id target caller => view layout id target (.integer caller)
  | .invalid => invalid layout

theorem literal_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) (frame : Frame) :
    HasType context (literal layout frame) layout.type definitions := by
  cases frame with
  | empty => exact empty_hasType context registered
  | state index => exact state_hasType registered .integer
  | view id target caller => exact view_hasType registered id target .integer
  | invalid => exact invalid_hasType context registered

def plainDispatch (table : Table) (layout : Layout) (origin : Word) (lexical : Expr) : List LambdaEdge → Expr
  | [] => invalid layout
  | edge :: rest =>
    if edge.origin = origin then
      .ifE (.binary .integerEq lexical (.integer (Int.ofNat edge.state)))
        (literal layout (checkedState table edge.state)) (plainDispatch table layout origin lexical rest)
    else plainDispatch table layout origin lexical rest

def viewDispatch (table : Table) (layout : Layout) (origin : Word) (id caller lexical : Expr) : List ViewEdge → Expr
  | [] => invalid layout
  | edge :: rest =>
    let tail := viewDispatch table layout origin id caller lexical rest
    if edge.target = origin then
      .ifE
        (.ifE (.binary .wordEq id (.word edge.view))
          (.ifE (.binary .integerEq caller (.integer (Int.ofNat edge.caller)))
            (.binary .integerEq lexical (.integer (Int.ofNat edge.lexical))) (.bool false)) (.bool false))
        (literal layout (checkedState table edge.destination)) tail
    else tail

/-- The lexical snapshot is decoded once. A matching transient view joins its
read-time caller index with that lexical index using the cached paired edges.
Other incoming frames use only an authenticated ordinary lambda edge. -/
def lambdaFrame (table : Table) (layout : Layout) (origin : Word) (lexical current : Expr) : Expr :=
  let plain := plainDispatch table layout origin (.var 1) table.lambdas
  .matchData layout.dataType layout.type lexical
    [invalid layout,
      .matchData layout.dataType layout.type (current.weakenAt 0)
        [plain, plain,
          .ifE (.binary .wordEq (.first (.second (.var 0))) (.word origin))
            (viewDispatch table layout origin (.first (.var 0)) (.second (.second (.var 0))) (.var 1) table.views)
            plain,
          plain],
      invalid layout, invalid layout]

/-- A read retains the current state index as a transient caller snapshot.
Empty/invalid/transient carriers cannot authenticate a source read context. -/
def readView (layout : Layout) (id target : Word) (current : Expr) : Expr :=
  .matchData layout.dataType layout.type current
    [invalid layout, view layout id target (.var 0), invalid layout, invalid layout]

def readFrame (id target : Word) : Frame → Frame
  | .state index => .view id target index
  | _ => .invalid

private theorem atFront {definitions : DataEnvironment} {context : Context} {expression : Expr} {type : Ty}
    (typed : HasType context expression type definitions) (inserted : Ty) :
    HasType (inserted :: context) (expression.weakenAt 0) type definitions := by
  simpa [Context.insertAt] using typed.weakenAt (inserted := inserted) 0

theorem plainDispatch_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (table : Table) (origin : Word) {lexical : Expr}
    (typed : HasType context lexical .integer definitions) (rows : List LambdaEdge) :
    HasType context (plainDispatch table layout origin lexical rows) layout.type definitions := by
  induction rows with
  | nil => exact invalid_hasType context registered
  | cons edge rest ih =>
    simp only [plainDispatch]
    split
    · exact .ifE (.binary typed .integer) (literal_hasType context registered _) ih
    · exact ih

theorem viewDispatch_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (table : Table) (origin : Word) {id caller lexical : Expr}
    (idTyped : HasType context id .word definitions)
    (callerTyped : HasType context caller .integer definitions)
    (lexicalTyped : HasType context lexical .integer definitions) (rows : List ViewEdge) :
    HasType context (viewDispatch table layout origin id caller lexical rows) layout.type definitions := by
  induction rows with
  | nil => exact invalid_hasType context registered
  | cons edge rest ih =>
    simp only [viewDispatch]
    split
    · exact .ifE (.ifE (.binary idTyped .word)
        (.ifE (.binary callerTyped .integer) (.binary lexicalTyped .integer) .bool) .bool)
        (literal_hasType context registered _) ih
    · exact ih

theorem lambdaFrame_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (table : Table) (origin : Word) {lexical current : Expr}
    (lexicalTyped : HasType context lexical layout.type definitions)
    (currentTyped : HasType context current layout.type definitions) :
    HasType context (lambdaFrame table layout origin lexical current) layout.type definitions := by
  apply HasType.matchData registered.lookup registered.typeWellFormed lexicalTyped
  apply BranchesHaveType.cons (invalid_hasType _ registered)
  apply BranchesHaveType.cons
  · apply HasType.matchData registered.lookup registered.typeWellFormed (atFront currentTyped .integer)
    apply BranchesHaveType.cons (plainDispatch_hasType registered table origin (.var rfl) _)
    apply BranchesHaveType.cons (plainDispatch_hasType registered table origin (.var rfl) _)
    apply BranchesHaveType.cons
    · exact .ifE (.binary (.first (.second (.var rfl))) .word)
        (viewDispatch_hasType registered table origin (.first (.var rfl))
          (.second (.second (.var rfl))) (.var rfl) _)
        (plainDispatch_hasType registered table origin (.var rfl) _)
    · exact .cons (plainDispatch_hasType registered table origin (.var rfl) _) .nil
  · exact .cons (invalid_hasType _ registered) (.cons (invalid_hasType _ registered) .nil)

theorem readView_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (id target : Word) {current : Expr}
    (typed : HasType context current layout.type definitions) :
    HasType context (readView layout id target current) layout.type definitions := by
  apply HasType.matchData registered.lookup registered.typeWellFormed typed
  exact .cons (invalid_hasType _ registered) (.cons (view_hasType registered id target (.var rfl))
    (.cons (invalid_hasType _ registered) (.cons (invalid_hasType _ registered) .nil)))

/-- This sealed recipe points to the existing checked metadata preparation.
It adds no independent source evidence and does not rebuild the graph. -/
structure Dispatch {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} (graph : Graph base) where private mk ::
  table : Table
  tableOwner : table = graph.table

def prepare {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} (graph : Graph base) : Dispatch graph :=
  ⟨graph.table, rfl⟩

end Solcore.Frontend.SourceCoreCallableIndexedDispatch
