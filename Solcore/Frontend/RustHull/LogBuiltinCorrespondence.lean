import Solcore.Frontend.RustHull.LogsCorrespondence
import Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
import Solcore.Frontend.RustHull.ParameterRenamingCorrespondence

/-! Event capture through actual Hull builtin lowering, including the static
write guard and the runtime registers used by exceptional termination. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LogBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence LogsCorrespondence

structure Locations where
  logs : LogsCorrespondence.Locations
  address : Nat
  isStatic : Nat
  exit : Nat
  returnOffset : Nat
  returnSize : Nat

def Locations.all (locations : Locations) : List Nat :=
  locations.logs.all ++ [locations.address, locations.isStatic, locations.exit,
    locations.returnOffset, locations.returnSize]

def Locations.mutable (locations : Locations) : List Nat :=
  locations.logs.all ++ [locations.exit, locations.returnOffset, locations.returnSize]

structure StateRel (locations : Locations) (state : LogsSemantics.State) (store : Store) : Prop where
  logs : LogsCorrespondence.StateRel locations.logs state store
  address : store.read? locations.address = some (.word state.address)
  isStatic : store.read? locations.isStatic = some (.bool state.isStatic)
  exit : store.read? locations.exit = some (.word state.exit)
  returnOffset : store.read? locations.returnOffset = some (.word state.returnOffset)
  returnSize : store.read? locations.returnSize = some (.word state.returnSize)
  distinct : locations.all.Nodup

structure Frame (locations : Locations) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  preserved : ∀ location value, location ∉ locations.mutable →
    initial.read? location = some value → final.read? location = some value

theorem Frame.of_logs {locations : Locations} {initial final : Store}
    (frame : LogsCorrespondence.Frame locations.logs initial final) : Frame locations initial final :=
  ⟨frame.length, fun location value outside found => frame.read location value
    (fun member => outside (List.mem_append_left _ member)) found⟩

set_option linter.unusedSimpArgs false in
private theorem StateRel.withLogs {locations : Locations} {state finalState : LogsSemantics.State}
    {offset length : Word} {topics : List Word} {result : Semantics.Result Semantics.Value}
    {initial final : Store} (related : StateRel locations state initial)
    (appended : LogsSemantics.Append offset length topics state result finalState)
    (logs : LogsCorrespondence.StateRel locations.logs finalState final)
    (frame : LogsCorrespondence.Frame locations.logs initial final) : StateRel locations finalState final := by
  have distinct := related.distinct
  simp only [Locations.all, LogsCorrespondence.Locations.all, List.cons_append, List.nil_append,
    List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at distinct
  have address := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.address
  have isStatic := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.isStatic
  have exit := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.exit
  have returnOffset := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.returnOffset
  have returnSize := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.returnSize
  cases appended <;> exact ⟨logs, address, isStatic, exit, returnOffset, returnSize, related.distinct⟩

def haltStore (locations : Locations) (store : Store) : Store :=
  StorageBuiltinCorrespondence.haltCells locations.exit locations.returnOffset locations.returnSize store

theorem haltStore_other {locations : Locations} {store : Store} {location : Nat} {value : Core.Value}
    (exit : location ≠ locations.exit) (offset : location ≠ locations.returnOffset) (size : location ≠ locations.returnSize)
    (found : store.read? location = some value) :
    (haltStore locations store).read? location = some value := by
  simp only [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?,
    List.getElem?_set_ne (Ne.symm exit), List.getElem?_set_ne (Ne.symm offset), List.getElem?_set_ne (Ne.symm size)]
  exact found

theorem haltStore_frame (locations : Locations) (store : Store) : Frame locations store (haltStore locations store) := by
  constructor
  · simp [haltStore, StorageBuiltinCorrespondence.haltCells]
  · intro location value outside found
    simp [Locations.mutable] at outside
    exact haltStore_other outside.2.1 outside.2.2.1 outside.2.2.2 found

theorem StateRel.halt {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) :
    StateRel locations {state with exit := Word.ofNatModulo 3, returnOffset := Word.zero, returnSize := Word.zero}
      (haltStore locations store) := by
  have distinct := related.distinct
  simp [Locations.all, LogsCorrespondence.Locations.all] at distinct
  have offsetBound := (List.getElem?_eq_some_iff.mp related.returnOffset).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.returnSize).1
  have exitBound := (List.getElem?_eq_some_iff.mp related.exit).1
  constructor
  · constructor
    · exact related.logs.distinct
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.memory
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.memorySize
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.logs
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.logSize
  · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.address
  · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.isStatic
  · simp [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?, exitBound]
  · simp only [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?,
      List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnOffset),
      List.getElem?_set_ne (by intro same; simp_all : locations.returnSize ≠ locations.returnOffset)]
    simp [offsetBound]
  · simp only [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?,
      List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnSize)]
    simp [sizeBound]
  · exact related.distinct

private theorem log_components (operation : LogsSemantics.Operation) {scope : Scope}
    {offset length : Core.Expr} {topics : List Core.Expr} {lowered : Lowered}
    (count : topics.length = operation.count)
    (compiled : Effects.lowerBuiltin scope operation.name (offset :: length :: topics) = .ok lowered) :
    ∃ memory memorySize logs logSize address isStatic stop,
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok memorySize ∧
      Effects.reference scope "logs" WordMapping.type = .ok logs ∧
      Effects.reference scope "logSize" .word = .ok logSize ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "isStatic" .bool = .ok isStatic ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop ∧
      lowered = ⟨.unit, .ifE (.loadCell isStatic) stop
        (Logs.append memory memorySize logs logSize (.loadCell address) topics offset length)⟩ := by
  let action : LowerM Lowered := do
    let memory ← Effects.reference scope "memory" WordMapping.type
    let memorySize ← Effects.reference scope "memorySize" .word
    let logs ← Effects.reference scope "logs" WordMapping.type
    let logSize ← Effects.reference scope "logSize" .word
    let address ← Effects.reference scope "address" .word
    let isStatic ← Effects.reference scope "isStatic" .bool
    let stop ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
    pure (Lowered.mk .unit (.ifE (.loadCell isStatic) stop
      (Logs.append memory memorySize logs logSize (.loadCell address) topics offset length)))
  have checked : ((if topics.length = operation.count then action
      else (fail "wrong number of log topics" : LowerM Unit) >>= fun _ => action) >>=
      fun raw => pure raw) = .ok lowered := by
    cases operation <;> exact compiled
  obtain ⟨raw, checked, returned⟩ := lower_bind_eq_ok.mp checked
  cases returned
  have components : action = .ok lowered := by
    simpa only [count, ↓reduceIte] using checked
  unfold action at components
  obtain ⟨memory, memoryCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨memorySize, memorySizeCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨logs, logsCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨logSize, logSizeCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨isStatic, isStaticCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨stop, stopCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨memory, memorySize, logs, logSize, address, isStatic, stop, memoryCompiled, memorySizeCompiled,
    logsCompiled, logSizeCompiled, addressCompiled, isStaticCompiled, stopCompiled, (Except.ok.inj returned).symm⟩


theorem inner_preserves (operation : LogsSemantics.Operation)
    {scope : Scope} {offsetExpr lengthExpr : Core.Expr} {topicExprs : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name (offsetExpr :: lengthExpr :: topicExprs) = .ok lowered)
    {offset length : Word} {topics : List Word} (count : topics.length = operation.count)
    {state finalState : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (executed : LogsSemantics.Execute offset length topics state result finalState)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, locations.logs.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.logs.memorySize⟩ ∈ slots)
    (logsMember : ⟨"logs", WordMapping.type, locations.logs.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, locations.logs.logSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (offsetEvaluated : Evaluates environment store (offsetExpr.rename mapping) (.word offset) store)
    (lengthEvaluated : Evaluates environment store (lengthExpr.rename mapping) (.word length) store)
    (topicsRelated : WordExpressions environment (topicExprs.map (·.rename mapping)) topics) :
    ∃ target finalStore, ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target finalStore ∧
      StateRel locations finalState finalStore ∧ Frame locations store finalStore := by
  have topicLength : topicExprs.length = topics.length := by simpa using topicsRelated.length
  obtain ⟨memory, memorySize, logs, logSize, address, isStatic, stop,
    memoryCompiled, memorySizeCompiled, logsCompiled, logSizeCompiled, addressCompiled,
    staticCompiled, stopCompiled, rfl⟩ := log_components operation (topicLength.trans count) compiled
  cases executed with
  | static readOnly =>
      have distinct := stateRelated.distinct
      simp [Locations.all, LogsCorrespondence.Locations.all] at distinct
      refine ⟨.inLeft .unit (.word Word.maximum), haltStore locations store, .language _, ?_,
        stateRelated.halt, haltStore_frame _ _⟩
      apply Evaluates.ifTrue
      · exact .loadCell (reference_evaluates runtime staticMember staticCompiled store)
          (by simpa only [readOnly] using stateRelated.isStatic)
      · exact StorageBuiltinCorrespondence.stop_evaluates_cells stopCompiled runtime memorySizeMember
          exitMember offsetMember sizeMember stateRelated.exit stateRelated.returnOffset stateRelated.returnSize
          (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all)
  | writable writable appended =>
      have allowed : topicExprs.length ≤ 4 := by rw [topicLength, count]; cases operation <;> decide
      obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, framed⟩ :=
        append_preserves appended stateRelated.logs
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember memorySizeCompiled store)
          (reference_evaluates runtime logsMember logsCompiled store)
          (reference_evaluates runtime logSizeMember logSizeCompiled store)
          (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
          offsetEvaluated lengthEvaluated topicsRelated
      refine ⟨target, finalStore, resultRelated, ?_, stateRelated.withLogs appended finalRelated framed, Frame.of_logs framed⟩
      apply Evaluates.ifFalse
      · exact .loadCell (reference_evaluates runtime staticMember staticCompiled store)
          (by simpa only [writable] using stateRelated.isStatic)
      · rw [append_rename _ _ _ _ _ _ _ _ _ allowed]
        exact evaluated

private theorem wordPacket_eq_bundle (values : List Word) :
    wordPacket values = ScalarExecution.bundleValues (values.map Core.Value.word) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next rest => exact congrArg (Core.Value.pair (.word head)) ih

private theorem field_eq_project (index count : Nat) (expression : Core.Expr) :
    Logs.field index count expression = projectArgument index count expression := by
  induction count generalizing index expression with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          by_cases first : index = 0 <;> simp [Logs.field, projectArgument, first, ih]


/-- Source event execution is preserved by the actual public builtin compiler,
including its argument packing and temporary-scope renaming. -/
theorem preserves (operation : LogsSemantics.Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {offset length : Word} {topics : List Word} (count : topics.length = operation.count)
    {state finalState : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (executed : LogsSemantics.Execute offset length topics state result finalState)
    {targets : List Core.Value}
    (related : ArgumentsRel arguments (.word offset :: .word length :: topics.map Semantics.Value.word) targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {initial store : Store}
    {locations : Locations} (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, locations.logs.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.logs.memorySize⟩ ∈ slots)
    (logsMember : ⟨"logs", WordMapping.type, locations.logs.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, locations.logs.logSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore, ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      StateRel locations finalState finalStore ∧ Frame locations store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  obtain ⟨expressions, values, argumentsEqual, sourcesEqual, targetsEqual, lengths⟩ := word_arguments related words
  have valuesEqual : values = offset :: length :: topics :=
    (List.map_inj_right (fun _ _ equal => Semantics.Value.word.inj equal)).mp sourcesEqual.symm
  subst values
  have argumentsLength : arguments.length = (offset :: length :: topics).length := by
    rw [argumentsEqual, List.length_map, lengths]
  subst targets
  rw [← wordPacket_eq_bundle] at packed
  generalize projectedEqual : (List.range arguments.length).map
    (fun index => projectArgument index arguments.length (.var 0)) = projected at rawCompiled
  have fields : WordExpressions (wordPacket (offset :: length :: topics) :: environment)
      (projected.map (·.rename mapping.lift)) (offset :: length :: topics) := by
    have expressionsEqual : projected.map (·.rename mapping.lift) =
        (List.range (offset :: length :: topics).length).map
          (fun index => Logs.field index (offset :: length :: topics).length (.var 0)) := by
      rw [← projectedEqual, argumentsLength, List.map_map]
      apply List.map_congr_left
      intro index _
      simp only [Function.comp_apply]
      rw [projectArgument_rename, field_eq_project]
      rfl
    rw [expressionsEqual]
    exact (Stable.var (by rfl)).fields
  cases projected with
  | nil => cases fields
  | cons offsetExpr remaining =>
      cases remaining with
      | nil => cases fields with | cons first rest => cases rest
      | cons lengthExpr topicExprs =>
          cases fields with
          | cons first rest =>
            cases rest with
            | cons second topicFields =>
              obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, framed⟩ :=
                inner_preserves operation rawCompiled count executed
                  (runtime.temporary (packArguments arguments).type (wordPacket (offset :: length :: topics)))
                  memoryMember memorySizeMember logsMember logSizeMember addressMember staticMember
                  exitMember offsetMember sizeMember stateRelated (first.evaluates store) (second.evaluates store) topicFields
              cases typed
              cases loweredEqual
              exact ⟨target, finalStore, resultRelated, LanguageResult.bind_success raw.type packed evaluated,
                finalRelated, framed⟩

end Solcore.Frontend.RustHull.LogBuiltinCorrespondence
