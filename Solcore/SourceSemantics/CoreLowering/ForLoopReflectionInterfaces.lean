import Solcore.SourceSemantics.CoreLowering.LoopReflectionInterfaces
import Solcore.SourceSemantics.CoreLowering.ForLoopCoreEdges
import Solcore.SourceSemantics.CoreLowering.ForPostMeaning

/-! Internal proof contracts for finite for iteration reflection. The body
contract is discharged by statement-tree induction; the post contract below
is constructed directly from its static header tree. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

inductive ForMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {finalContext outcome after result}
      (execution : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after)
      (related : ControlRepresents type outcome result) :
      ForMeaning program context evidence source reasonAt environment before condition post statements type finalContext outcome after result
  | fault {reason after word}
      (fault : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      ForMeaning program context evidence source reasonAt environment before condition post statements type context (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

def ForResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    ForMeaning program context evidence source reasonAt environment before condition post statements type finalContext outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def PostConstructs (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word)
    (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (items : List ForItemForm) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    ∀ continued : Bool,
      ForHeaders.PostResult program context evidence source reasonAt environment heap items type mapping world
        ((if continued then ForLoop.continuingPrefix type else ForLoop.fallthroughPrefix type) ++
          Core.LoopExecution.entryEnvironment type location actual) store (ForLoop.postCode code)

theorem post_constructs
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {items : List ForItemForm} {code : Core.Expr} {ξ : Core.Renaming}
    (tree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context items code)
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    PostConstructs program context evidence source reasonAt scope administrativeContext environment canonical actual actualContext
      type location items (code.rename ξ) := by
  intro mapping world heap store environments heaps actualTyped locationTyped continued
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have entry := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  cases continued with
  | false =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType)
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.construct_post program evidence valid environments heaps shifted
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.fallthroughPrefix, Core.LoopExecution.entryEnvironment,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] using result
  | true =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inRight (leftType := Core.LocalControl.controlType type)
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit))).insert
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.construct_post program evidence valid environments heaps shifted
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.continuingPrefix, Core.LoopExecution.entryEnvironment,
      ↓reduceIte, List.cons_append, List.nil_append] using result

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
