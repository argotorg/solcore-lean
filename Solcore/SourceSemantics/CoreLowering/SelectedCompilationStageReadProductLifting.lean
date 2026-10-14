import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageGroupLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadProductBounds
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageReadProductLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds Staging.Recursive.Lifting
open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)
universe u

private theorem literal_atomic {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    Staging.Recursive.AtomicForm node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .reference _ _
  | word value form _ _ _ _ => rw [form]; exact .literal _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integerLiteral _ _

private theorem literal_coercions {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem literal_nonlocal {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    ∀ name binder, node.form ≠ .reference name (.local binder) := by
  cases literal with
  | unit form _ _ _ | bool _ form _ _ _ | word _ form _ _ _ _
  | resolvedWord form _ | resolvedInteger form _ => intros; simp [form]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Certificate readFuel
  (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  invocation.source context solved reasonAt

include extension sameLedger runtimeLedger unique in
/-- Every leaf and pair prefix is reconstructed from the actual ordinary trace
and physical state. All results and semantic failures retain the exact heap. -/
theorem exact_trace {scope id lowered} (certificate : trees scope id lowered) :
    ∀ {node}, invocation.source.lookupExpression? id = some node →
      ExpressionHasType invocation.source context id node.type →
    ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext
        scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
      GenericHeap.HeapRepresents valueModel mapping world before store →
      Dynamic.EnvironmentAgrees before context.locals environment →
      EnvironmentsAgree ξ canonical actual →
      RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source environment before id outcome after →
      Staging.Recursive.Expression program registry invocation context environment before id (embed outcome) after := by
  obtain ⟨tree, sites⟩ := certificate
  induction sites with
  | literal _ receipt =>
    intro node found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    obtain ⟨actualNode, actualFound, literal, _⟩ := receipt
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound actualFound)
      (literal_atomic literal) (literal_coercions literal) (literal_nonlocal literal) trace
  | read receipt =>
    intro node found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    obtain ⟨certificate, _, binding⟩ := receipt
    obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
    obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
      GenericHeap.lookup_visible environments heaps lookup certificate.slot
    cases read.functional selectedRead
    exact Staging.Recursive.Lifting.atomic_read unique (lookupExpression?_sound certificate.metadata.found)
      certificate.form certificate.metadata.coercions lookup read cellRep.ordinary trace
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    intro actualNode found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨otherNode, otherFound, _, childTyped⟩ := CompatibleExpressionProducts.group_source_types
      unique metadata.found form metadata.coercions typed
    cases Option.some.inj (otherFound.symm.trans innerFound)
    exact .group ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      (ih innerFound childTyped environments heaps locals agrees actualTyped initial admitted
        (CompatibleExpressionProducts.group_inv metadata form unique trace))
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
    intro actualNode found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨firstNode, secondNode, firstFound, secondFound, _, leftTyped, rightTyped⟩ :=
      CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
    cases Option.some.inj (firstFound.symm.trans leftFound)
    cases Option.some.inj (secondFound.symm.trans rightFound)
    have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [left, right]) :=
      ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
    have tailLift : ∀ {a middle},
        Dynamic.ExpressionEvaluates program context invocation.evidence invocation.source environment before left a middle →
        ∀ {outcome after}, Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
          environment middle right outcome after →
        Staging.Recursive.Expression program registry invocation context environment before left (.value a) middle ∧
        Staging.Recursive.Expression program registry invocation context environment middle right (embed outcome) after := by
      intro a middle evaluated outcome after tail
      have lifted := leftIH leftFound leftTyped environments heaps locals agrees actualTyped initial admitted (.value evaluated)
      obtain ⟨size, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, _, represented, middleHeaps,
        maps, worlds, _, metadata, reached, _, post⟩ :=
        SelectedCompilationReadProductBounds.preserves bridge functions extension sameLedger runtimeLedger
          (semanticFaults := fun _ _ => True) (fun _ _ => True) (by intros; trivial)
          (by intros; trivial) unique size ⟨leftTree, leftSites⟩ leftFound leftTyped
          environments heaps locals agrees actualTyped initial admitted measured
      cases represented with
      | value payload =>
        exact ⟨lifted, rightIH rightFound rightTyped (environments.extend maps worlds) middleHeaps
          (locals.mono metadata) agrees (actualTyped.weaken worlds) reached post.at_value.2 tail⟩
    obtain ⟨sequence, children, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    cases packed with
    | values pack =>
      cases children with
      | values children =>
        cases children with
        | cons first rest =>
          cases rest with
          | cons second rest =>
            cases rest
            cases pack with
            | cons tail =>
              cases tail
              obtain ⟨leftLift, rightLift⟩ := tailLift first (.value second)
              exact .pair occurrence leftLift rightLift
    | fault reason =>
      cases children with
      | fault failed =>
        cases failed with
        | head head =>
          exact .pairLeftFault occurrence
            (leftIH leftFound leftTyped environments heaps locals agrees actualTyped initial admitted (.fault head))
        | tail head tail =>
          cases tail with
          | head failed =>
            obtain ⟨leftLift, rightLift⟩ := tailLift head (.fault failed)
            exact .pairRightFault occurrence leftLift rightLift
          | tail _ impossible => cases impossible

include extension sameLedger runtimeLedger unique in
theorem lifts (size : Nat) : LiftsAt bridge context valueModel registry invocation trees size := by
  intro scope id lowered certificate node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  exact .completed (exact_trace bridge functions extension sameLedger runtimeLedger unique certificate found typed
    environments heaps locals agrees actualTyped initial admitted trace.sound)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageReadProductLifting
