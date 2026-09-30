import Solcore.SourceSemantics.CoreLowering.LoopStatementFault
import Solcore.SourceSemantics.CoreLowering.LoopCoreInversion

/-! Proof contracts for reconstruction of independent source executions from
finite generated Core executions. These contracts are internal induction
hypotheses; compiler acceptance will supply them through the static tree. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal

def Executes (functionMode : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : Context)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  if functionMode then Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after
  else Dynamic.StatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after

inductive OutcomeRepresents (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) : Dynamic.ControlOutcome → Core.Value → Prop where
  | control {outcome value} (related : ControlRepresents type outcome value) :
      OutcomeRepresents program evidence source reasonAt type outcome value
  | fault {reason word} (related : FaultRepresents program evidence source reasonAt reason word) :
      OutcomeRepresents program evidence source reasonAt type (.fault reason) (.inLeft (Core.LocalLoop.controlType type) (.word word))

/-- Pair each source judgment with its corresponding result constructor. This
prevents a fault witness from being supplied through the successful judgment. -/
inductive Meaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (functionMode : Bool)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {finalContext outcome after result}
      (execution : ScalarStatementViews.ListExecutes functionMode program context evidence source environment before statements finalContext outcome after)
      (related : ControlRepresents type outcome result) :
      Meaning program context evidence source reasonAt functionMode environment before statements type finalContext outcome after result
  | fault {finalContext reason after word}
      (execution : ScalarStatementViews.ListFaults functionMode program context evidence source environment before statements finalContext reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      Meaning program context evidence source reasonAt functionMode environment before statements type finalContext (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

theorem Meaning.source
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {mode : Bool} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {statements : List StatementId} {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (meaning : Meaning program context evidence source reasonAt mode environment before statements type finalContext outcome after result) :
    Executes mode program context evidence source environment before statements finalContext outcome after := by
  cases meaning with
  | control execution _ => cases mode <;> exact .control execution
  | fault execution _ => cases mode <;> exact .fault execution

theorem Meaning.related
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {mode : Bool} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {statements : List StatementId} {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (meaning : Meaning program context evidence source reasonAt mode environment before statements type finalContext outcome after result) :
    OutcomeRepresents program evidence source reasonAt type outcome result := by
  cases meaning with
  | control _ related => exact .control related
  | fault _ related => exact .fault related

def Result (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (functionMode : Bool) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    Meaning program context evidence source reasonAt functionMode environment before statements type finalContext outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def Reflects (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (functionMode : Bool) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Core.Evaluates actual store (code.rename ξ) result finalStore →
    Result program context evidence source reasonAt functionMode environment heap statements type mapping world store result finalStore

/-- Reconstruct one loop body's finite source execution from its actual Core
execution, including the three temporary binders at loop entry. -/
def BodyReflects (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word)
    (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (statements : List StatementId) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
    {store finalStore : Core.Store} {result : Core.Value},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    Core.Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode code) result finalStore →
    Result program context evidence source reasonAt false environment heap statements type mapping world store result finalStore

theorem Reflects.body
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {statements : List StatementId} {code : Core.Expr} {ξ : Core.Renaming}
    (correct : Reflects compilation program evidence source reasonAt scope context false statements type code)
    (wellFormed : Core.Ty.WellFormed [] type) (valid : PrimitiveExpressions.ContextValid compilation context)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    BodyReflects program context evidence source reasonAt scope administrativeContext environment canonical actual actualContext
      type location statements (code.rename ξ) := by
  intro mapping world heap store finalStore result environments heaps actualTyped locationTyped evaluation
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have shifted := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  apply correct wellFormed valid environments heaps shifted
  simpa only [rename_insert, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, Core.LoopExecution.bodyCode] using evaluation

inductive WhileMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (statements : List StatementId) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {finalContext outcome after result}
      (execution : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after)
      (related : ControlRepresents type outcome result) :
      WhileMeaning program context evidence source reasonAt environment before condition statements type finalContext outcome after result
  | fault {reason after word}
      (fault : Dynamic.WhileFaults program context evidence source environment before condition statements reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      WhileMeaning program context evidence source reasonAt environment before condition statements type context (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

def WhileResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    WhileMeaning program context evidence source reasonAt environment before condition statements type finalContext outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
