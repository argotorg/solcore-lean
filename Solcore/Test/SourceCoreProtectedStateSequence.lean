import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion

/-! Effectful consumers of the existing ordered sequence induction. The head
lazily initializes an ordinary mapping cell; the next read observes that write.
Records are determined by the actual initialized source/native cells, so the
original witness cannot be reused at the reached heap. Repeated labels remain
ordered list entries. A nonmapping uninitialized read exercises tail failure. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
namespace Tests.SourceCoreProtectedStateSequence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof GenericExpressionMeaning DataExpressionSequence
open ProtectedDataExpressionSequence ProtectedStateTransition

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"protected_sequence", by decide⟩], by decide⟩⟩, 0⟩
private def id (n : Nat) : ExpressionId := ⟨⟨owner, n⟩⟩
private def binder (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "protected_sequence.solc"⟩, 0, 1⟩
private def mapType : TypeSystem.Ty := .mapping .word .word
private def emptyMap : Dynamic.Value := .mapping .word .word []
private def token : Word := Word.ofNatModulo 7
private def payload : Value := .word (Word.ofNatModulo 42)
private def sourceNode (n : Nat) : ExpressionNode := {
  id := id n, span, type := if n = 2 then .word else mapType,
  form := .reference "local" (.local (binder n)) }
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0), .expression (id 1), .expression (id 2)],
  nodes := [.expression (sourceNode 0), .expression (sourceNode 1), .expression (sourceNode 2)] }
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def projects : GenericHeap.Projection := fun source native =>
  native = .word ∧ (source = mapType ∨ source = .word)
private def model : GenericHeap.PayloadModel catalog projects [] where
  Represents _ _ source value native type :=
    source = mapType ∧ value = emptyMap ∧ native = payload ∧ type = .word
  projection := by rintro _ _ _ _ _ _ ⟨rfl, _, _, rfl⟩; exact ⟨rfl, Or.inl rfl⟩
  runtime_hasType := by rintro _ _ _ _ _ _ ⟨_, _, rfl, rfl⟩; exact .word
  extend := fun represented _ _ => represented
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def scheme (type : TypeSystem.Ty) : TypeSystem.Scheme := { quantified := [], body := type }
private def context : SourceSemantics.Context := {
  Context.ofSignatures signatures with
  locals := [(binder 0, scheme mapType), (binder 1, scheme mapType), (binder 2, scheme .word)] }
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceEnv : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def scope : SourceCoreLocalCell.Scope := [(binder 0, .word), (binder 1, .word), (binder 2, .word)]
private def world : StoreTyping := List.replicate 3 (OptionalCell.cellType .word)
private def mapping : LocationMap := [0, 1, 2]
private def canonical : Environment := [.cellRef (OptionalCell.cellType .word) 0,
  .cellRef (OptionalCell.cellType .word) 1, .cellRef (OptionalCell.cellType .word) 2]
private structure Stage where
  first : Bool
  second : Bool
private def heapAt (stage : Stage) : Dynamic.Heap := ⟨[
  ⟨mapType, if stage.first then some emptyMap else none, none⟩,
  ⟨mapType, if stage.second then some emptyMap else none, none⟩,
  ⟨.word, none, none⟩]⟩
private def storeAt (stage : Stage) : Store := [
  if stage.first then .inRight .unit payload else .inLeft .word .unit,
  if stage.second then .inRight .unit payload else .inLeft .word .unit,
  .inLeft .word .unit]
private def indexAt (stage : Stage) : Index := ⟨scope, mapping, world, heapAt stage, storeAt stage, canonical⟩
private def recordsAt (stage : Stage) : List Nat :=
  (if stage.first then [42] else []) ++ (if stage.second then [42] else [])
private def Advance (before after : Stage) : Prop :=
  (before.first = true → after.first = true) ∧ (before.second = true → after.second = true)
private def protocol : Protocol (List Nat) where
  State index := { stage : Stage // indexAt stage = index }
  records state := recordsAt state.val
  Relates first last := Advance first.val last.val
  refl _ := ⟨fun h => h, fun h => h⟩
  trans first last := ⟨fun value => last.1 (first.1 value), fun value => last.2 (first.2 value)⟩
private def atStage (stage : Stage) : protocol.State (indexAt stage) := ⟨stage, rfl⟩
private def nextStage (stage : Stage) (slot : Fin 3) : Stage :=
  if slot.val = 0 then ⟨true, stage.second⟩ else if slot.val = 1 then ⟨stage.first, true⟩ else stage
private def codeAt (slot : Fin 3) : SourceCoreBasic.LoweredExpr := ⟨.word,
  if slot.val = 2 then OptionalCell.read .word (.var 2) token
  else SourceCoreCompatibleDataExpressions.readMapping (.var slot.val) (.word (Word.ofNatModulo 42))⟩
private def faultRep : FaultRep := fun reason value => reason = .uninitializedLocation ⟨2⟩ ∧ value = token
private inductive Child : Certificate where
  | read (slot : Fin 3) : Child scope (id slot.val) (codeAt slot)

private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source, sourceNode, Node.occurrenceId, Node.id, NodeId.occurrenceId, id]
private theorem found (slot : Fin 3) : source.lookupExpression? (id slot.val) = some (sourceNode slot.val) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp only [Fin.val_mk] <;> decide
private theorem mapped_index {n target : Nat} (found : mapping[n]? = some target) : n = target := by
  have bounded := (List.getElem?_eq_some_iff.mp found).1
  change n < 3 at bounded
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp [mapping] at found <;> omega
private theorem environment_exact {admin environment stage}
    (represented : DataHeap.EnvRepresents catalog mapping world admin scope environment canonical [])
    (locals : Dynamic.EnvironmentAgrees (heapAt stage) context.locals environment) : environment = sourceEnv := by
  cases locals with
  | @cons _ _ _ _ location0 _ _ _ _ tail =>
    cases tail with
    | @cons _ _ _ _ location1 _ _ _ _ tail =>
      cases tail with
      | @cons _ _ _ _ location2 _ _ _ _ tail =>
        cases tail
        cases represented with
        | internal _ absent _ => exact (absent location0 .head).elim
        | cons first rest =>
          cases rest with
          | internal _ absent _ => exact (absent location1 .head).elim
          | cons second rest =>
            cases rest with
            | internal _ absent _ => exact (absent location2 .head).elim
            | cons third rest =>
              cases rest
              have zero := mapped_index first.mapped
              have one := mapped_index second.mapped
              have two := mapped_index third.mapped
              cases location0; cases location1; cases location2
              simp only at zero one two
              subst_vars
              rfl
private theorem source_lookup (slot : Fin 3) : Dynamic.Environment.LooksUp sourceEnv (binder slot.val) ⟨slot.val⟩ := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp only [Fin.val_mk]
  · exact .head
  · exact .tail (by decide) .head
  · exact .tail (by decide) (.tail (by decide) .head)
private theorem source_read (stage : Stage) (slot : Fin 3) :
    Dynamic.Heap.Reads (heapAt stage) ⟨slot.val⟩
      (if slot.val = 2 then ⟨.word, none, none⟩ else
        ⟨mapType, if (if slot.val = 0 then stage.first else stage.second) then some emptyMap else none, none⟩) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp only [Fin.val_mk]
  · exact .intro .head
  · exact .intro (.tail .head)
  · exact .intro (.tail (.tail .head))

private theorem mapping_cell (flag : Bool) (locations : LocationMap) (typing : StoreTyping) :
    GenericHeap.CellRepresents model locations typing
      ⟨mapType, if flag then some emptyMap else none, none⟩
      (if flag then .inRight .unit payload else .inLeft .word .unit) .word := by
  cases flag
  · exact .uninitialized ⟨rfl, Or.inl rfl⟩
  · exact .initialized ⟨rfl, rfl, rfl, rfl⟩
private theorem heap_rep (stage : Stage) :
    GenericHeap.HeapRepresents model mapping world (heapAt stage) (storeAt stage) := by
  have first := (GenericHeap.HeapRepresents.empty (model := model)).allocate
    (mapping_cell stage.first [] []) Dynamic.Heap.Allocates.append
  have second := first.1.allocate
    (mapping_cell stage.second _ _) Dynamic.Heap.Allocates.append
  have third := second.1.allocate
    (GenericHeap.CellRepresents.uninitialized (model := model) ⟨rfl, Or.inr rfl⟩) Dynamic.Heap.Allocates.append
  exact third.1
private def sourceOutcome (slot : Fin 3) : Dynamic.ExpressionOutcome :=
  if slot.val = 2 then .fault (.uninitializedLocation ⟨2⟩) else .value emptyMap
private def coreOutcome (slot : Fin 3) : Value :=
  if slot.val = 2 then .inLeft .word (.word token) else .inRight .word payload
private def traceSize (slot : Fin 3) : Nat := if slot.val = 2 then 2 else 3
private theorem advance (stage : Stage) (slot : Fin 3) : Advance stage (nextStage stage slot) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp [Advance, nextStage]
private theorem raw_source (stage : Stage) (slot : Fin 3) :
    ExpressionTraceAt program (traceSize slot) context [] source sourceEnv (heapAt stage)
      (id slot.val) (sourceOutcome slot) (heapAt (nextStage stage slot)) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · cases first : stage.first
    · refine .value (.intro (lookupExpression?_sound (found ⟨0, by decide⟩)) ?_ .nil)
      exact .localEmptyMapping rfl (source_lookup ⟨0, by decide⟩)
        (source_read stage ⟨0, by decide⟩) rfl rfl (by simp [first])
        (.intro (source_read stage ⟨0, by decide⟩) (by simpa [heapAt, nextStage, first, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
          (Dynamic.Heap.CellsWrite.head : Dynamic.Heap.CellsWrite (heapAt stage).cells 0
            ⟨mapType, some emptyMap, none⟩ (heapAt ⟨true, stage.second⟩).cells)))
    · refine .value (.intro (lookupExpression?_sound (found ⟨0, by decide⟩)) ?_ .nil)
      simpa [heapAt, nextStage, first, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
        (SourceExecutionSize.ExpressionFormEvaluates.local (program := program) (context := context)
          (evidence := []) (source := source) (value := emptyMap) (name := "local") (requirements := []) (coercions := []) rfl (source_lookup ⟨0, by decide⟩)
          (source_read stage ⟨0, by decide⟩) rfl (by simp [first]))
  · cases second : stage.second
    · refine .value (.intro (lookupExpression?_sound (found ⟨1, by decide⟩)) ?_ .nil)
      exact .localEmptyMapping rfl (source_lookup ⟨1, by decide⟩)
        (source_read stage ⟨1, by decide⟩) rfl rfl (by simp [second])
        (.intro (source_read stage ⟨1, by decide⟩) (by simpa [heapAt, nextStage, second, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
          (Dynamic.Heap.CellsWrite.tail Dynamic.Heap.CellsWrite.head : Dynamic.Heap.CellsWrite (heapAt stage).cells 1
            ⟨mapType, some emptyMap, none⟩ (heapAt ⟨stage.first, true⟩).cells)))
    · refine .value (.intro (lookupExpression?_sound (found ⟨1, by decide⟩)) ?_ .nil)
      simpa [heapAt, nextStage, second, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
        (SourceExecutionSize.ExpressionFormEvaluates.local (program := program) (context := context)
          (evidence := []) (source := source) (value := emptyMap) (name := "local") (requirements := []) (coercions := []) rfl (source_lookup ⟨1, by decide⟩)
          (source_read stage ⟨1, by decide⟩) rfl (by simp [second]))
  · exact .fault (.form (lookupExpression?_sound (found ⟨2, by decide⟩))
      (.localUninitialized (owned := []) rfl (source_lookup ⟨2, by decide⟩)
        (source_read stage ⟨2, by decide⟩) rfl rfl (by intro ⟨_, _, impossible⟩; cases impossible)))
private theorem native (stage : Stage) (slot : Fin 3) {actual : Environment} {ξ : Renaming}
    (layout : EnvironmentsAgree ξ canonical actual) :
    Evaluates actual (storeAt stage) ((codeAt slot).expression.rename ξ)
      (coreOutcome slot) (storeAt (nextStage stage slot)) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · change Evaluates actual (storeAt stage)
      ((SourceCoreCompatibleDataExpressions.readMapping (.var 0) (.word (Word.ofNatModulo 42))).rename ξ)
      (.inRight .word payload) (storeAt ⟨true, stage.second⟩)
    rw [CompatibleExpressionReadCompletion.mapping_rename (CompatibleMapping.VirtualRoot.Quoted.word (Word.ofNatModulo 42))]
    cases first : stage.first
    · simpa [storeAt, payload, first, List.set] using
        SourceCoreCompatibleDataExpressions.readMapping_initializes (payload := .word)
          (before := storeAt stage) (middle := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 0) rfl)) (by simp [storeAt, Store.read?, first])
          (by simpa [Expr.weakenAt, Expr.rename, payload] using
            (Core.Evaluates.word : Evaluates _ (storeAt stage) (Expr.word (Word.ofNatModulo 42))
              (.word (Word.ofNatModulo 42)) (storeAt stage)))
          (by simp [storeAt, Store.read?, first])
    · simpa [storeAt, first] using
        SourceCoreCompatibleDataExpressions.readMapping_present (payload := .word)
          (before := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 0) rfl)) (by simp [storeAt, Store.read?, first])
  · change Evaluates actual (storeAt stage)
      ((SourceCoreCompatibleDataExpressions.readMapping (.var 1) (.word (Word.ofNatModulo 42))).rename ξ)
      (.inRight .word payload) (storeAt ⟨stage.first, true⟩)
    rw [CompatibleExpressionReadCompletion.mapping_rename (CompatibleMapping.VirtualRoot.Quoted.word (Word.ofNatModulo 42))]
    cases second : stage.second
    · simpa [storeAt, payload, second, List.set] using
        SourceCoreCompatibleDataExpressions.readMapping_initializes (payload := .word)
          (before := storeAt stage) (middle := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 1) rfl)) (by simp [storeAt, Store.read?, second])
          (by simpa [Expr.weakenAt, Expr.rename, payload] using
            (Core.Evaluates.word : Evaluates _ (storeAt stage) (Expr.word (Word.ofNatModulo 42))
              (.word (Word.ofNatModulo 42)) (storeAt stage)))
          (by simp [storeAt, Store.read?, second])
    · simpa [storeAt, second] using
        SourceCoreCompatibleDataExpressions.readMapping_present (payload := .word)
          (before := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 1) rfl)) (by simp [storeAt, Store.read?, second])
  · change Evaluates actual (storeAt stage) ((OptionalCell.read .word (.var 2) token).rename ξ)
      (.inLeft .word (.word token)) (storeAt stage)
    simpa [OptionalCell.read, LanguageResult.failure, LanguageResult.success, Expr.rename, Renaming.lift] using
      OptionalCell.read_failure token (.var (layout (index := 2) rfl)) (by simp [storeAt, Store.read?])

private theorem metadata (first last : Stage) : Dynamic.HeapMetadataExtend (heapAt first) (heapAt last) := by
  intro location cell read
  cases location
  cases read with
  | intro read =>
    cases read with
    | head => exact ⟨_, .intro .head, rfl, rfl⟩
    | tail read =>
      cases read with
      | head => exact ⟨_, .intro (.tail .head), rfl, rfl⟩
      | tail read =>
        cases read with
        | head => exact ⟨_, .intro (.tail (.tail .head)), rfl, rfl⟩
        | tail read => cases read
private theorem frame (first last : Stage) : AdministrativePreserved mapping (storeAt first) mapping (storeAt last) := by
  intro location absent bounded
  change location < 3 at bounded
  change Nat at location
  have choices : location = 0 ∨ location = 1 ∨ location = 2 := by
    have small : location ≤ 2 := Nat.le_of_lt_succ bounded
    rcases Nat.le_succ_iff.mp small with small | last
    · rcases Nat.le_succ_iff.mp small with zero | one
      · exact Or.inl (Nat.eq_zero_of_le_zero zero)
      · exact Or.inr (Or.inl one)
    · exact Or.inr (Or.inr last)
  rcases choices with rfl | rfl | rfl <;> exact (absent (by decide)).elim
private theorem result (_stage : Stage) (slot : Fin 3) :
    ResultRepresents model mapping world (sourceNode slot.val).type (codeAt slot).type faultRep
      (sourceOutcome slot) (coreOutcome slot) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · exact .value ⟨rfl, rfl, rfl, rfl⟩
  · exact .value ⟨rfl, rfl, rfl, rfl⟩
  · exact .fault ⟨rfl, rfl⟩
private theorem child_preserves (size : Nat) :
    Stateful.ExpressionPreservesAt protocol size model program context [] source Child faultRep := by
  intro selectedScope expression lowered generated foundNode foundNodeEq locations typing admin environment oldCanonical
    actual actualContext before store ξ outcome after environments heaps locals layout actualTyped initial trace
  cases generated with
  | read slot =>
    have sameNode : foundNode = sourceNode slot.val := Option.some.inj (foundNodeEq.symm.trans (found slot))
    subst foundNode
    rcases initial with ⟨stage, sameIndex⟩
    have sameMap := congrArg Index.mapping sameIndex
    have sameWorld := congrArg Index.world sameIndex
    have sameHeap := congrArg Index.heap sameIndex
    have sameStore := congrArg Index.store sameIndex
    have sameCanonical := congrArg Index.canonical sameIndex
    dsimp [indexAt] at sameMap sameWorld sameHeap sameStore sameCanonical
    subst locations; subst typing; subst before; subst store; subst oldCanonical
    have sameEnvironment := environment_exact environments locals
    subst environment
    have same := CompatibleExpressionReads.source_outcome_unique unique (lookupExpression?_sound (found slot))
      (show (sourceNode slot.val).form = .reference "local" (.local (binder slot.val)) from rfl) rfl
      (source_lookup slot) (source_read stage slot) (by split <;> rfl) trace.sound (raw_source stage slot).sound
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨coreOutcome slot, storeAt (nextStage stage slot), mapping, world, native stage slot layout,
      result stage slot, heap_rep (nextStage stage slot), .refl _, .refl _, frame stage _, metadata stage _,
      ⟨atStage (nextStage stage slot), advance stage slot⟩⟩
private theorem child_reflects (size : Nat) :
    Stateful.ExpressionReflectsAt protocol size model program context [] source Child faultRep := by
  intro selectedScope expression lowered generated foundNode foundNodeEq locations typing admin environment oldCanonical
    actual actualContext before store ξ value finalStore environments heaps locals layout actualTyped initial evaluated
  cases generated with
  | read slot =>
    have sameNode : foundNode = sourceNode slot.val := Option.some.inj (foundNodeEq.symm.trans (found slot))
    subst foundNode
    rcases initial with ⟨stage, sameIndex⟩
    have sameMap := congrArg Index.mapping sameIndex
    have sameWorld := congrArg Index.world sameIndex
    have sameHeap := congrArg Index.heap sameIndex
    have sameStore := congrArg Index.store sameIndex
    have sameCanonical := congrArg Index.canonical sameIndex
    dsimp [indexAt] at sameMap sameWorld sameHeap sameStore sameCanonical
    subst locations; subst typing; subst before; subst store; subst oldCanonical
    have sameEnvironment := environment_exact environments locals
    subst environment
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (native stage slot layout)
    exact ⟨traceSize slot, sourceOutcome slot, heapAt (nextStage stage slot), mapping, world,
      raw_source stage slot, result stage slot, heap_rep (nextStage stage slot), .refl _, .refl _,
      frame stage _, metadata stage _, ⟨atStage (nextStage stage slot), advance stage slot⟩⟩

private def start : Stage := ⟨false, false⟩
private def middle : Stage := ⟨true, false⟩
private def finish : Stage := ⟨true, true⟩
private theorem environments : DataHeap.EnvRepresents catalog mapping world [] scope sourceEnv canonical [] :=
  .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil .nil)))
private theorem locals (stage : Stage) : Dynamic.EnvironmentAgrees (heapAt stage) context.locals sourceEnv :=
  .cons (source_read stage ⟨0, by decide⟩) rfl (.ordinary rfl rfl)
    (.cons (source_read stage ⟨1, by decide⟩) rfl (.ordinary rfl rfl)
      (.cons (source_read stage ⟨2, by decide⟩) rfl (.ordinary rfl rfl) .nil))
private theorem layout : EnvironmentsAgree Renaming.id canonical canonical := fun same => same
private theorem actualTyped : RuntimeEnvironmentHasTypes world canonical (SourceCoreLocalCell.coreContext scope) [] :=
  environments.runtime_hasTypes
private theorem stage_of_heap {first last : Stage} (same : heapAt first = heapAt last) : first = last := by
  rcases first with ⟨a, b⟩
  rcases last with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [heapAt] <;> rfl
private theorem records_from_heap {index : Index} (state : protocol.State index) (stage : Stage)
    (same : index.heap = heapAt stage) : protocol.records state = recordsAt stage := by
  obtain ⟨earlier, found⟩ := state
  have equal := stage_of_heap ((congrArg Index.heap found).trans same)
  cases equal
  rfl
private theorem source_success : SourceExecutionSize.ExpressionsEvaluate program 9 context [] source sourceEnv
    (heapAt start) [id 0, id 1] [emptyMap, emptyMap] (heapAt finish) := by
  have first := raw_source start ⟨0, by decide⟩
  have last := raw_source middle ⟨1, by decide⟩
  cases first with
  | value first =>
    cases last with
    | value last => exact .cons first (.cons last .nil)
private theorem source_fault : SourceExecutionSize.ExpressionsFault program 7 context [] source sourceEnv
    (heapAt start) [id 0, id 2] (.uninitializedLocation ⟨2⟩) (heapAt middle) := by
  have first := raw_source start ⟨0, by decide⟩
  have last := raw_source middle ⟨2, by decide⟩
  cases first with
  | value first =>
    cases last with
    | fault last => exact .tail first (.head last)
private theorem source_duplicate : SourceExecutionSize.ExpressionsEvaluate program 9 context [] source sourceEnv
    (heapAt start) [id 0, id 0] [emptyMap, emptyMap] (heapAt middle) := by
  have first := raw_source start ⟨0, by decide⟩
  have last := raw_source middle ⟨0, by decide⟩
  cases first with
  | value first =>
    cases last with
    | value last => exact .cons first (.cons last .nil)
private theorem pair_tree (last : Fin 3) : DataExpressionSequence.Tree source Child scope
    [id 0, id last.val] [(sourceNode 0).type, (sourceNode last.val).type]
    [codeAt ⟨0, by decide⟩, codeAt last] :=
  .cons (found ⟨0, by decide⟩) (.read ⟨0, by decide⟩) (.single (found last) (.read last))
private theorem native_pair (last : Fin 3) :
    Evaluates canonical (storeAt start)
      (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt last]).expression
      (if last.val = 2 then .inLeft (.product .word .word) (.word token)
        else .inRight .word (.pair payload payload)) (storeAt (nextStage middle last)) := by
  have first := native start ⟨0, by decide⟩ layout
  have lastEval := native middle last (agree_prefix layout payload)
  rw [rename_prefix] at lastEval
  simp only [Expr.rename_id] at first lastEval
  rcases last with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · exact LocalSequence.pair_success _ _ first lastEval
  · exact LocalSequence.pair_success _ _ first lastEval
  · exact LocalSequence.pair_right_failure _ _ first lastEval

/-- The head's list append is tied to real source/native initialization. -/
theorem head_appends_42 :
    ExpressionTraceAt program 3 context [] source sourceEnv (heapAt start) (id 0)
      (.value emptyMap) (heapAt middle) ∧
    Evaluates canonical (storeAt start) (codeAt ⟨0, by decide⟩).expression
      (.inRight .word payload) (storeAt middle) ∧
    protocol.records (atStage middle) = protocol.records (atStage start) ++ [42] ∧
    protocol.Relates (atStage start) (atStage middle) := by
  exact ⟨raw_source start ⟨0, by decide⟩, by simpa [coreOutcome, nextStage, start, middle] using native start ⟨0, by decide⟩ layout,
    rfl, advance start ⟨0, by decide⟩⟩
/-- Reusing the original state after the head would contradict its real heap index. -/
theorem original_witness_cannot_reach_middle :
    ¬ indexAt start = indexAt middle := by
  intro same
  have impossible := stage_of_heap (congrArg Index.heap same)
  cases impossible

/-- The tail input at the head's reached index is exactly its concrete
initialization witness, including the [42] observation. -/
theorem middle_witness_is_exact (reached : protocol.State (indexAt middle)) :
    reached = atStage middle := by
  apply Subtype.ext
  exact stage_of_heap (congrArg Index.heap reached.property)

/-- At the exact inclusive source budget, both effects survive in order. The
identical labels come from different real mapping initialization writes. -/
theorem successful_cons_preserves_duplicate_records :
    ∃ value finalStore finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, heapAt finish, finalStore, canonical⟩,
      Evaluates canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩]).expression value finalStore ∧
      DataExpressionSequence.Result model finalMap finalWorld [mapType, mapType]
        [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩] faultRep (.ok [emptyMap, emptyMap]) value ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42, 42] := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.preserves_bounded protocol 9 (pair_tree ⟨1, by decide⟩)
      (fun size _ => child_preserves size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (.values source_success) (Nat.le_refl 9)
  obtain ⟨final, related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, final, by simpa using evaluated, represented, related,
    records_from_heap final finish rfl⟩
/-- A tail failure retains the witness produced by the successful head. -/
theorem tail_fault_retains_head_record :
    ∃ value finalStore finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, heapAt middle, finalStore, canonical⟩,
      Evaluates canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩]).expression value finalStore ∧
      DataExpressionSequence.Result model finalMap finalWorld [mapType, .word]
        [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩] faultRep (.error (.uninitializedLocation ⟨2⟩)) value ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42] := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.preserves_bounded protocol 7 (pair_tree ⟨2, by decide⟩)
      (fun size _ => child_preserves size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (.fault source_fault) (Nat.le_refl 7)
  obtain ⟨final, related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, final, by simpa using evaluated, represented, related,
    records_from_heap final middle rfl⟩
/-- Duplicate expression IDs are evaluated in sequence; the second read sees
the initialized cell and creates no second record for that same write. -/
theorem repeated_child_uses_reached_heap :
    ∃ value finalStore finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, heapAt middle, finalStore, canonical⟩,
      Evaluates canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨0, by decide⟩]).expression value finalStore ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42] := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.preserves_bounded protocol 9 (pair_tree ⟨0, by decide⟩)
      (fun size _ => child_preserves size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (.values source_duplicate) (Nat.le_refl 9)
  obtain ⟨final, related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, final, by simpa using evaluated, related,
    records_from_heap final middle rfl⟩

private theorem stage_of_store {first last : Stage} (same : storeAt first = storeAt last) : first = last := by
  rcases first with ⟨a, b⟩
  rcases last with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [storeAt] <;> rfl
private theorem records_from_store {index : Index} (state : protocol.State index) (stage : Stage)
    (same : index.store = storeAt stage) : protocol.records state = recordsAt stage := by
  obtain ⟨earlier, found⟩ := state
  have equal := stage_of_store ((congrArg Index.store found).trans same)
  cases equal
  rfl
/-- Native completion, measured strictly below its budget, reconstructs a
source trace and the two records fixed by its real final store. -/
theorem successful_cons_reflects_duplicate_records :
    ∃ nativeSize sourceSize outcome after finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, after, storeAt finish, canonical⟩,
      EvaluationSize nativeSize canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩]).expression
        (.inRight .word (.pair payload payload)) (storeAt finish) ∧
      nativeSize < nativeSize + 1 ∧
      TraceAt program sourceSize context [] source sourceEnv (heapAt start) [id 0, id 1] outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld [mapType, mapType]
        [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩] faultRep outcome (.inRight .word (.pair payload payload)) ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42, 42] := by
  have completed : Evaluates canonical (storeAt start)
      (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩]).expression
      (.inRight .word (.pair payload payload)) (storeAt finish) := native_pair ⟨1, by decide⟩
  obtain ⟨nativeSize, sized⟩ := evaluation_has_size completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.reflects_bounded protocol (nativeSize + 1) (pair_tree ⟨1, by decide⟩)
      (fun size _ => child_reflects size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (by simpa using sized) (Nat.lt_succ_self nativeSize)
  obtain ⟨final, related⟩ := transition
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, final, sized, Nat.lt_succ_self nativeSize,
    trace, represented, related, records_from_store final finish rfl⟩
/-- A real native right-branch fault reflects to the same source failure and
retains the record from the earlier initialization write. -/
theorem tail_fault_reflects_head_record :
    ∃ nativeSize sourceSize after finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, after, storeAt middle, canonical⟩,
      EvaluationSize nativeSize canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩]).expression
        (.inLeft (.product .word .word) (.word token)) (storeAt middle) ∧
      nativeSize < nativeSize + 1 ∧
      TraceAt program sourceSize context [] source sourceEnv (heapAt start) [id 0, id 2]
        (.error (.uninitializedLocation ⟨2⟩)) after ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42] := by
  have completed : Evaluates canonical (storeAt start)
      (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩]).expression
      (.inLeft (.product .word .word) (.word token)) (storeAt middle) := native_pair ⟨2, by decide⟩
  obtain ⟨nativeSize, sized⟩ := evaluation_has_size completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.reflects_bounded protocol (nativeSize + 1) (pair_tree ⟨2, by decide⟩)
      (fun size _ => child_reflects size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (by simpa using sized) (Nat.lt_succ_self nativeSize)
  obtain ⟨final, related⟩ := transition
  cases represented with
  | fault matched =>
    obtain ⟨rfl, _⟩ := matched
    exact ⟨nativeSize, sourceSize, after, finalMap, finalWorld, final, sized, Nat.lt_succ_self nativeSize,
      trace, related, records_from_store final middle rfl⟩

#print axioms child_preserves
#print axioms child_reflects
#print axioms raw_source
#print axioms native_pair
#print axioms head_appends_42
#print axioms original_witness_cannot_reach_middle
#print axioms middle_witness_is_exact
#print axioms successful_cons_preserves_duplicate_records
#print axioms tail_fault_retains_head_record
#print axioms repeated_child_uses_reached_heap
#print axioms successful_cons_reflects_duplicate_records
#print axioms tail_fault_reflects_head_record
end Tests.SourceCoreProtectedStateSequence
