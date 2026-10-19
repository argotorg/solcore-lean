import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPairBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedExpressionBounds

/-! Pair results inherit typing and heap admission from the actual ordered
children, including callable values and their complete captures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPairBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareStagedExpressionBounds
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionProducts (Metadata)
open CallableIndexedOwnedPreparedStagedPairBounds (Pair ProductValues)
universe u

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {cells : GenericHeap.CellModel definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- A payload model may combine two represented values at the same reached
heap/world. This is a representation constructor, with no execution input. -/
private inductive SourceChildren (size : Nat) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | leftFault {childSize after failure}
      (smaller : childSize < size)
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before left (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | rightFault {firstSize secondSize middle after value failure}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value value) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | values {firstSize secondSize middle after leftValue rightValue}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value leftValue) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.value rightValue) after) :
      SourceChildren size environment before left right (.value (.product leftValue rightValue)) after

private theorem source_children
    {id left right : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .tuple [left, right])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    SourceChildren (program := program) (registry := registry) (invocation := invocation)
      (context := context) size environment before left right outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .tuple [left, right] := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at localForm
      cases localForm
  | pair occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .values (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | pairLeftFault occurrence child =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .leftFault (Staging.Recursive.Size.child_lt_stepSize (by simp)) child
  | pairRightFault occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .rightFault (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | tupleValue occurrence sequence packed =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail
              cases packed with
              | cons last =>
                  cases last
                  exact .values (by simp [Staging.Recursive.Size.stepSize]; omega)
                    (by simp [Staging.Recursive.Size.stepSize]; omega) first second
  | tupleFault occurrence sequence =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | headFault first =>
          exact .leftFault (by simp [Staging.Recursive.Size.stepSize]; omega) first
      | tailFault first rest =>
          cases rest with
          | headFault second =>
              exact .rightFault (by simp [Staging.Recursive.Size.stepSize]; omega)
                (by simp [Staging.Recursive.Size.stepSize]; omega) first second
          | tailFault _ rest => cases rest
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _
  | group occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typing
    {id left right : ExpressionId} {node leftNode rightNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .tuple [left, right])
    (leftFound : invocation.source.lookupExpression? left = some leftNode)
    (rightFound : invocation.source.lookupExpression? right = some rightNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context left leftNode.type ∧
      ExpressionHasType invocation.source context right rightNode.type := by
  obtain ⟨first, second, firstFound, secondFound, _sourceType, firstTyped, secondTyped⟩ :=
    CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
  cases Option.some.inj (firstFound.symm.trans leftFound)
  cases Option.some.inj (secondFound.symm.trans rightFound)
  exact ⟨firstTyped, secondTyped⟩

/-- Two genuine Source children are executed in their actual successive heaps.
Either failure keeps its original scoped representation and exact endpoint. -/
theorem pair_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : PreservesBelow bridge context model cells registry invocation children faults budget) :
    ∀ size, size ≤ budget → PreservesAt bridge context model cells registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have parts := source_children unique metadata.found form trace
      cases parts with
      | leftFault smaller first =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le smaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
              rw [DataExpressionSequence.pair_rename]
              exact LocalSequence.pair_left_failure _ _ evaluated
      | rightFault firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 second
              cases represented with
              | fault matched =>
                  refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related,
                    post.at_fault_type⟩
                  rw [DataExpressionSequence.pair_rename]
                  rw [rename_prefix] at secondEval
                  exact LocalSequence.pair_right_failure _ _ firstEval secondEval
      | values firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 second
              cases represented with
              | @value lastSource lastCoreValue lastPayload =>
                  refine ⟨.inRight .word (.pair coreValue lastCoreValue), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related, ?_⟩
                  · rw [DataExpressionSequence.pair_rename]
                    rw [rename_prefix] at secondEval
                    exact LocalSequence.pair_success _ _ firstEval secondEval
                  · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                  · refine ⟨post.rows, ?_⟩
                    intro value same
                    cases same
                    refine ⟨?_, post.at_value.2.heap⟩
                    rw [sourceType]
                    exact .product (firstPost.at_value.1.mono heapMetadata) post.at_value.1

/-- Actual native bind inversion supplies strictly smaller executed children;
the Source pair grade is constructed independently from their Source traces. -/
theorem pair_reflects
    (unique : NodeOccurrencesUnique invocation.source)
    (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : ReflectsBelow bridge context model cells registry invocation children faults budget) :
    ∀ size, size ≤ budget → ReflectsAt bridge context model cells registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [_, _]) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      change EvaluationSize size actual store ((LocalSequence.pair _ _ _ _).rename ξ) value finalStore at completed
      rw [DataExpressionSequence.pair_rename] at completed
      have complete := completed
      cases completed with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure _ _ first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .pairLeftFault occurrence trace,
                .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related,
                post.at_fault_type⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted
                  cases represented with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure _ _ first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld,
                        .pairRightFault occurrence firstTrace secondTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related,
                        post.at_fault_type⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted
                  cases represented with
                  | @value lastSource lastCoreValue lastPayload =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success _ _ first.sound second.sound)
                      have trace := Staging.Recursive.Size.Expression.pair occurrence firstTrace secondTrace
                      refine ⟨_, .value _, after, finalMap, finalWorld, trace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related, ?_⟩
                      · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                      · refine ⟨post.rows, ?_⟩
                        intro value same
                        cases same
                        refine ⟨?_, post.at_value.2.heap⟩
                        rw [sourceType]
                        exact .product (firstPost.at_value.1.mono heapMetadata) post.at_value.1

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPairBounds
