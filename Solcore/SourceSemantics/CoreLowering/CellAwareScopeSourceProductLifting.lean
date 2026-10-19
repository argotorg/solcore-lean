import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopePairBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds

/-! Ordered ordinary Source children lift at their actual reached physical
state. A stage rejection stops the enclosing product at that same prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceProductLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open Staging.Recursive.Lifting
open CellAwareScopeSourceLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedGroupBounds (Group)
open CallableIndexedOwnedPreparedStagedPairBounds (Pair)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

theorem group (unique : NodeOccurrencesUnique invocation.source)
    (childLift : ∀ size, LiftsAt bridge context model named registry invocation children size)
    (size : Nat) :
    LiftsAt bridge context model named registry invocation (Group compiled.compatible.checked invocation.source children) size := by
  intro scope id lowered certificate actualNode found typed mapping world administrative environment canonical actual actualContext
    before store embedding outcome after environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  cases certificate with
  | actual metadata form innerFound sourceType certified =>
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨innerNode, actualFound, _, innerTyped⟩ := CompatibleExpressionProducts.group_source_types
      unique metadata.found form metadata.coercions typed
    cases Option.some.inj (actualFound.symm.trans innerFound)
    obtain ⟨childSize, measured⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
      (CompatibleExpressionProducts.group_inv metadata form unique trace.sound)
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift childSize certified innerFound innerTyped
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame measured
    exact ⟨staged, reached, .group ⟨_, lookupExpression?_sound metadata.found, form,
      metadata.requirements, metadata.coercions⟩ lifted, adapted⟩

theorem pair (unique : NodeOccurrencesUnique invocation.source)
    (childLift : ∀ size, LiftsAt bridge context model named registry invocation children size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation children faults size)
    (size : Nat) :
    LiftsAt bridge context model named registry invocation (Pair compiled.compatible.checked invocation.source children) size := by
  intro scope id lowered certificate actualNode found typed mapping world administrative environment canonical actual actualContext
    before store embedding outcome after environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  cases certificate with
  | @actual node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstChild secondChild =>
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨leftNode, rightNode, actualLeft, actualRight, _, leftTyped, rightTyped⟩ :=
      CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
    cases Option.some.inj (actualLeft.symm.trans leftFound)
    cases Option.some.inj (actualRight.symm.trans rightFound)
    have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [left, right]) :=
      ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
    have leftLift : ∀ {plain reached}, Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before left plain reached → ExpressionLift program registry invocation context environment before left plain reached := by
      intro plain reached child
      obtain ⟨childSize, measured⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size child
      exact childLift childSize firstChild leftFound leftTyped environments heaps locals agrees actualTyped
        initial admitted authority physical owner ownerFrame measured
    have rightLift : ∀ {a middle},
        Staging.Recursive.Expression program registry invocation context environment before left (.value a) middle →
        ∀ {plain reached}, Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
          environment middle right plain reached → ExpressionLift program registry invocation context environment middle right plain reached := by
      intro a middle first plain reached second
      obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace first
      obtain ⟨value, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, _related, post⟩ :=
        preservation stageSize firstChild leftFound leftTyped environments heaps locals agrees actualTyped
          initial admitted authority physical owner ownerFrame measured
      cases represented with
      | value _payload =>
        obtain ⟨childSize, measuredChild⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size second
        exact childLift childSize secondChild rightFound rightTyped (environments.extend maps worlds) middleHeaps
          (locals.mono metadata) agrees (actualTyped.weaken worlds) middleState post.at_value.2
          (authority.transport effect) (physical.transport effect frame) owner ownerFrame measuredChild
    obtain ⟨sequence, childrenTrace, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace.sound
    cases packed with
    | values pack =>
      cases childrenTrace with
      | values childrenTrace =>
        cases childrenTrace with
        | cons first rest =>
          cases rest with
          | cons second rest =>
            cases rest
            cases pack with
            | cons tail =>
              cases tail
              obtain ⟨_, _, firstLift, firstAdapted⟩ := leftLift (.value first)
              cases firstAdapted with
              | rejected origin call reason reached =>
                exact .rejected (.pairLeftFault occurrence firstLift)
              | completed =>
                obtain ⟨_, _, secondLift, secondAdapted⟩ := rightLift firstLift (.value second)
                cases secondAdapted with
                | rejected origin call reason reached =>
                  exact .rejected (.pairRightFault occurrence firstLift secondLift)
                | completed => exact .completed (.pair occurrence firstLift secondLift)
    | fault reason =>
      cases childrenTrace with
      | fault failed =>
        cases failed with
        | head failed =>
          obtain ⟨_, _, lifted, adapted⟩ := leftLift (.fault failed)
          cases adapted with
          | completed => exact .completed (.pairLeftFault occurrence lifted)
          | rejected origin call reason reached => exact .rejected (.pairLeftFault occurrence lifted)
        | tail first rest =>
          cases rest with
          | head failed =>
            obtain ⟨_, _, firstLift, firstAdapted⟩ := leftLift (.value first)
            cases firstAdapted with
            | rejected origin call reason reached => exact .rejected (.pairLeftFault occurrence firstLift)
            | completed =>
              obtain ⟨_, _, secondLift, secondAdapted⟩ := rightLift firstLift (.fault failed)
              cases secondAdapted with
              | rejected origin call reason reached => exact .rejected (.pairRightFault occurrence firstLift secondLift)
              | completed => exact .completed (.pairRightFault occurrence firstLift secondLift)
          | tail _ impossible => cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceProductLifting
