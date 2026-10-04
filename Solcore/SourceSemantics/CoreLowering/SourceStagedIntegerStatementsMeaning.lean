import Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreElaboration SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning

def bindingId (binding : Staged.Binding) : Resolved.LocalId := by
  cases binding with
  | mk binder _ => exact binder.id

theorem lookup_cons (binding : Staged.Binding) (actual : Staged.Environment) (id : Resolved.LocalId) :
    Staged.lookup (binding :: actual) id =
      if bindingId binding = id then some binding else Staged.lookup actual id := by
  change List.find? (fun item => decide (bindingId item = id)) (binding :: actual) =
    if bindingId binding = id then some binding else List.find? (fun item => decide (bindingId item = id)) actual
  by_cases same : bindingId binding = id <;> simp [List.find?, same]

/-- The actual first-match Integer environment tracks the independently
allocated source cell, including lexical shadowing and all old heap cells. -/
theorem EnvironmentRep.bind {actual : Staged.Environment} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} (binding : Staged.Binding)
    (related : EnvironmentRep actual environment heap)
    {afterEnvironment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocated : Dynamic.Binds environment heap (bindingId binding) .integer
      (some (.integer (bindingValue binding))) afterEnvironment after) :
    EnvironmentRep (binding :: actual) afterEnvironment after := by
  cases allocated with
  | intro allocation =>
    intro id selected found
    rw [lookup_cons] at found
    split at found
    · rename_i same
      have identical := Option.some.inj found
      cases identical
      exact ⟨_, _, same ▸ Dynamic.Environment.LooksUp.head, allocation.reads_new, rfl, rfl⟩
    · rename_i different
      obtain ⟨location, cell, lookup, read, ordinary, value⟩ := related id selected found
      exact ⟨location, cell, .tail different lookup, allocation.preserves_read read, ordinary, value⟩


/-- An actual immutable staged Integer cell carries no generalized closure. -/
def integerCell (value : Int) : Dynamic.Cell :=
  { type := .integer, value := some (.integer value) }

/-- Complete original heap and exact source-ordered appended Integer cells.
This is an allocation invariant, not an escape or whole-pass erasure law. -/
def Extends (before after : Dynamic.Heap) (values : List Int) : Prop :=
  after.cells = before.cells ++ values.map integerCell

namespace Extends

theorem refl (heap : Dynamic.Heap) : Extends heap heap [] := by
  simp [Extends]

theorem trans {before middle after : Dynamic.Heap} {left right : List Int}
    (first : Extends before middle left) (second : Extends middle after right) :
    Extends before after (left ++ right) := by
  simp only [Extends, List.map_append] at *
  rw [second, first, List.append_assoc]

theorem allocate {before middle after : Dynamic.Heap} {values : List Int}
    (extension : Extends before middle values) {value : Int} {location : Dynamic.Location}
    (allocated : Dynamic.Heap.Allocates middle .integer (some (.integer value)) location after) :
    Extends before after (values ++ [value]) := by
  cases allocated
  simpa only [Extends, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, integerCell] using congrArg (fun cells => cells ++ [integerCell value]) extension

theorem bind {before middle after : Dynamic.Heap} {values : List Int}
    (extension : Extends before middle values) {environment finalEnvironment : Dynamic.Environment}
    {id : Resolved.LocalId} {value : Int}
    (bound : Dynamic.Binds environment middle id .integer (some (.integer value)) finalEnvironment after) :
    Extends before after (values ++ [value]) := by
  cases bound with
  | intro allocated => exact extension.allocate allocated

theorem preserves_read {before after : Dynamic.Heap} {values : List Int}
    (extension : Extends before after values) {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads before location cell) : Dynamic.Heap.Reads after location cell := by
  cases read with
  | intro selected =>
      constructor
      rw [extension]
      exact selected.append_left

theorem length_eq {before after : Dynamic.Heap} {values : List Int}
    (extension : Extends before after values) : after.cells.length = before.cells.length + values.length := by
  change after.cells = before.cells ++ values.map integerCell at extension
  rw [extension, List.length_append, List.length_map]

end Extends

/-- Static lexical extensions on the exact accepted tree, with no execution law. -/
inductive BindingsFormed (solved : List SolvedRequirement) (source : TypedSource) :
    Solcore.SourceSemantics.Context → {actual : Staged.Environment} → {execute : Bool} → {fuel : Nat} →
    {roots : List StatementId} → {result : StagedIntegerEvaluation} →
    Staged.Statements.Checked solved source actual execute fuel roots result → Prop where
  | letValue {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {rest : List StatementId} {node : StatementNode}
      {binder : TypedBinder} {initializer : ExpressionId} {initial result : StagedIntegerEvaluation}
      {context next : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .letDecl binder (some initializer))
      (nodeType : node.type = .unit) (fresh : _)
      (owned : binder.id.owner = source.owner) (mono : binder.scheme.quantified = [])
      (binderType : binder.scheme.body = .integer)
      (initialChecked : Staged.IntegerChecked solved source actual execute fuel initializer initial)
      (bodyChecked : Staged.Statements.Checked solved source (Staged.Statements.bind binder initial.value :: actual) execute fuel rest result)
      (extension : BinderExtends source.owner context binder next)
      (bodyFormed : BindingsFormed solved source next bodyChecked) :
      BindingsFormed solved source context (.letValue found form nodeType fresh owned mono binderType initialChecked bodyChecked)
  | returnValue {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {value : ExpressionId}
      {result : StagedIntegerEvaluation} {context : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .returnStmt (some value)) (nodeType : node.type = .integer)
      (valueChecked : Staged.IntegerChecked solved source actual execute fuel value result) :
      BindingsFormed solved source context (.returnValue found form nodeType valueChecked)
  | conditional {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId}
      {yes no : List StatementId} {guard : StagedBoolEvaluation} {left right : StagedIntegerEvaluation}
      {context : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .ifThen condition yes (some no)) (nodeType : node.type = .integer)
      (conditionChecked : Staged.BoolChecked solved source actual execute fuel condition guard)
      (thenChecked : Staged.Statements.Checked solved source actual (execute && guard.value) fuel yes left)
      (elseChecked : Staged.Statements.Checked solved source actual (execute && !guard.value) fuel no right)
      (thenFormed : BindingsFormed solved source context thenChecked)
      (elseFormed : BindingsFormed solved source context elseChecked) :
      BindingsFormed solved source context (.conditional found form nodeType conditionChecked thenChecked elseChecked)
  | block {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {body : List StatementId}
      {result : StagedIntegerEvaluation} {context : Solcore.SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .block body) (nodeType : node.type = .integer)
      (bodyChecked : Staged.Statements.Checked solved source actual execute fuel body result)
      (bodyFormed : BindingsFormed solved source context bodyChecked) :
      BindingsFormed solved source context (.block found form nodeType bodyChecked)

/-- A lexical binder changes no assumptions or rule catalog used by a
consumed numeric implementation row. -/
theorem usedValid_extend {context next : Solcore.SourceSemantics.Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder} {solved : List SolvedRequirement} {used : List RequirementId}
    (extension : BinderExtends owner context binder next)
    (valid : UsedValid context solved used) : UsedValid next solved used := by
  cases extension
  intro row proof member consumed evidence
  cases valid row proof member consumed evidence with
  | intro authenticated => exact .intro authenticated


namespace StaticViews
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreElaboration SourceCoreElaboration.Internal

theorem checked_nonempty {solved source environment execute fuel statements result}
    (checked : Staged.Statements.Checked solved source environment execute fuel statements result) :
    statements ≠ [] := by
  cases checked <;> simp

theorem typed_cons {source control context final statement tail facts}
    (typed : StatementsHaveType source control context (statement :: tail) final facts)
    (nonempty : tail ≠ []) :
    ∃ middle headFacts tailFacts,
      StatementHasType source control context statement middle headFacts ∧
      StatementsHaveType source control middle tail final tailFacts := by
  cases typed with
  | singleton head => exact False.elim (nonempty rfl)
  | cons head rest => exact ⟨_, _, _, head, rest⟩

theorem typed_singleton {source control context final statement facts}
    (typed : StatementsHaveType source control context [statement] final facts) :
    ∃ headFacts, StatementHasType source control context statement final headFacts := by
  cases typed with
  | singleton head => exact ⟨_, head⟩

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other contains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique contains).symm.trans found)
  exact same ▸ sameForm

theorem typed_let {source control context final id facts node binder initializer}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (_mono : binder.scheme.quantified = [])
    (typed : StatementHasType source control context id final facts) :
    BinderExtends source.owner context binder final := by
  have shape := statement_shape unique found form
  clear found form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem typed_if {source control context final id facts node condition yes no}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition yes (some no))
    (typed : StatementHasType source control context id final facts) :
    ∃ yesFinal noFinal yesFacts noFacts,
      StatementsHaveType source control context yes yesFinal yesFacts ∧
      StatementsHaveType source control context no noFinal noFacts := by
  have shape := statement_shape unique found form
  clear found form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨⟨_, _, by assumption⟩, ⟨_, _, by assumption⟩⟩

theorem typed_block {source control context final id facts node statements}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (typed : StatementHasType source control context id final facts) :
    ∃ innerFinal innerFacts,
      StatementsHaveType source control context statements innerFinal innerFacts := by
  have shape := statement_shape unique found form
  clear found form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, by assumption⟩

end StaticViews

/-- Independent source typing supplies every lexical extension in the actual
checked tree, including branches validated without execution. -/
theorem bindingsFormed_of_typing {solved : List SolvedRequirement} {source : TypedSource}
    {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
    {roots : List StatementId} {result : StagedIntegerEvaluation}
    (checked : Staged.Statements.Checked solved source actual execute fuel roots result)
    (unique : NodeOccurrencesUnique source) {control : ControlContext}
    {context final : Solcore.SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context roots final facts) :
    BindingsFormed solved source context checked := by
  induction checked generalizing context final facts with
  | letValue found form nodeType fresh owned mono binderType initial body ih =>
      obtain ⟨next, headFacts, tailFacts, head, tail⟩ := StaticViews.typed_cons typed (StaticViews.checked_nonempty body)
      exact .letValue found form nodeType fresh owned mono binderType initial body
        (StaticViews.typed_let unique found form mono head) (ih tail)
  | returnValue found form nodeType value => exact .returnValue found form nodeType value
  | conditional found form nodeType condition yes no ihYes ihNo =>
      obtain ⟨headFacts, head⟩ := StaticViews.typed_singleton typed
      obtain ⟨yesFinal, noFinal, yesFacts, noFacts, yesTyped, noTyped⟩ := StaticViews.typed_if unique found form head
      exact .conditional found form nodeType condition yes no (ihYes yesTyped) (ihNo noTyped)
  | block found form nodeType body ih =>
      obtain ⟨headFacts, head⟩ := StaticViews.typed_singleton typed
      obtain ⟨inner, innerFacts, bodyTyped⟩ := StaticViews.typed_block unique found form head
      exact .block found form nodeType body (ih bodyTyped)

/-- Actual execution follows only the selected branch. It preserves every
initial cell and records the exact ordered suffix of allocated Integer cells. -/
theorem formed_meaning {solved : List SolvedRequirement} {source : TypedSource}
    {actual : Staged.Environment} {execute : Bool} {fuel : Nat}
    {roots : List StatementId} {result : StagedIntegerEvaluation}
    {checked : Staged.Statements.Checked solved source actual execute fuel roots result}
    {context : Solcore.SourceSemantics.Context}
    (formed : BindingsFormed solved source context checked) {program : Program}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (executed : execute = true) (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements) :
    ∃ final after added,
      Dynamic.StatementsExecute program context evidence source environment before roots final
        (.returned (.integer result.value)) after ∧ Extends before after added := by
  induction formed generalizing environment before with
  | @letValue actual execute fuel statement rest node binder initializer initial result context next found form nodeType fresh owned mono binderType initialChecked bodyChecked extension bodyFormed ih =>
      cases executed
      have initialValid : UsedValid context solved initial.consumedRequirements := valid.mono (by
        intro id member; exact List.mem_append_left _ member)
      have initialEval := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program) (evidence := evidence) ledger environments fuel).1 initialChecked initialValid
      let location : Dynamic.Location := ⟨before.cells.length⟩
      let middle : Dynamic.Heap := ⟨before.cells ++ [integerCell initial.value]⟩
      let nextEnvironment : Dynamic.Environment := (binder.id, location) :: environment
      have allocation : Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location middle := .append
      have binding : Dynamic.Binds environment before (bindingId (Staged.Statements.bind binder initial.value)) .integer
          (some (.integer (bindingValue (Staged.Statements.bind binder initial.value)))) nextEnvironment middle := by
        simpa only [bindingId, bindingValue, Staged.Statements.bind] using Dynamic.Binds.intro allocation
      have nextEnvironments := EnvironmentRep.bind (Staged.Statements.bind binder initial.value) environments binding
      have nextLedger := extension.context_fields.2.2.2.2.trans ledger
      have tailValid := usedValid_extend extension (valid.mono (by
        intro id member; exact List.mem_append_right _ member))
      obtain ⟨final, after, added, tailEval, cells⟩ := ih rfl nextLedger nextEnvironments tailValid
      have declaredAllocation : Dynamic.Heap.Allocates before binder.scheme.body
          (some (.integer initial.value)) location middle := by rw [binderType]; exact allocation
      have headEval : Dynamic.StatementExecutes program context evidence source environment before statement next
          (.fallthrough nextEnvironment) middle :=
        .letInitialized (lookupStatement?_sound found) form initialEval mono extension declaredAllocation
      exact ⟨final, after, [initial.value] ++ added, .cons headEval tailEval,
        (Extends.refl before).allocate allocation |>.trans cells⟩
  | returnValue found form nodeType valueChecked =>
      cases executed
      have evaluated := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program) (evidence := evidence) ledger environments _).1 valueChecked valid
      exact ⟨_, before, [], .terminal (.returnValue (lookupStatement?_sound found) form evaluated) (.returned _), Extends.refl before⟩
  | @conditional actual execute fuel statement node condition yes no guard left right context found form nodeType conditionChecked thenChecked elseChecked thenFormed elseFormed ihYes ihNo =>
      cases executed
      have guardValid : UsedValid context solved guard.consumedRequirements := valid.mono (by
        intro id member; exact List.mem_append_left _ (List.mem_append_left _ member))
      have guardEval := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program) (evidence := evidence) ledger environments fuel).2.2 conditionChecked guardValid
      cases truth : guard.value with
      | false =>
          have branchValid : UsedValid context solved right.consumedRequirements := valid.mono (by
            intro id member; exact List.mem_append_right _ member)
          obtain ⟨final, after, added, branchEval, cells⟩ := ihNo (by simp [truth]) ledger environments branchValid
          have headEval := Dynamic.StatementExecutes.ifFalseWithElse (lookupStatement?_sound found) form (by simpa only [truth] using guardEval) branchEval
          refine ⟨context, after, added, ?_, cells⟩
          simpa only [truth, Bool.false_eq_true, ↓reduceIte, Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
      | true =>
          have branchValid : UsedValid context solved left.consumedRequirements := valid.mono (by
            intro id member; exact List.mem_append_left _ (List.mem_append_right _ member))
          obtain ⟨final, after, added, branchEval, cells⟩ := ihYes (by simp [truth]) ledger environments branchValid
          have headEval := Dynamic.StatementExecutes.ifTrue (lookupStatement?_sound found) form (by simpa only [truth] using guardEval) branchEval
          refine ⟨context, after, added, ?_, cells⟩
          simpa only [truth, ↓reduceIte, Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
  | @block actual execute fuel statement node body result context found form nodeType bodyChecked bodyFormed ih =>
      obtain ⟨final, after, added, bodyEval, cells⟩ := ih executed ledger environments valid
      have headEval := Dynamic.StatementExecutes.block (lookupStatement?_sound found) form bodyEval
      refine ⟨context, after, added, ?_, cells⟩
      simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
open Solcore Solcore.Frontend Solcore.Frontend.SourceCoreElaboration.Internal
open Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning

private theorem lookup_bind (binder : SourceInference.TypedBinder) (value : Int)
    (actual : Staged.Environment) (id : Resolved.LocalId) :
    Staged.lookup (Staged.Statements.bind binder value :: actual) id =
      if binder.id = id then some (Staged.Statements.bind binder value)
      else Staged.lookup actual id := by
  change List.find? _ (Staged.Statements.bind binder value :: actual) = _
  by_cases same : binder.id = id <;> simp [List.find?, Staged.Statements.bind, same] <;> rfl

/-- Inputs are allocated in the original compiler order. The source environment
places later inputs first; freshness in the actual receipt preserves every
previous input lookup despite this reversal. -/
theorem allocate_seen {source : SourceInference.TypedSource} {seen : List Resolved.LocalId}
    {binders : List SourceInference.TypedBinder} {values : List Int} {actual : Staged.Environment}
    (checked : Staged.Statements.InputsChecked source seen binders values actual)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    ∃ finalEnvironment after,
      Dynamic.BindersAllocate environment before binders (values.map Dynamic.Value.integer) finalEnvironment after ∧
      EnvironmentRep actual finalEnvironment after ∧
      after.cells = before.cells ++ values.map integerCell ∧
      (∀ id, id ∈ seen → ∀ location, Dynamic.Environment.LooksUp environment id location →
        Dynamic.Environment.LooksUp finalEnvironment id location) := by
  induction checked generalizing environment before with
  | nil seen =>
    refine ⟨environment, before, .nil environment before, EnvironmentRep.empty environment before, ?_, ?_⟩
    · simp
    · intro id member location found; exact found
  | @cons seen binder rest value values actual owned fresh mono typed tail ih =>
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let middle : Dynamic.Heap := ⟨before.cells ++ [integerCell value]⟩
    have allocate : Dynamic.Heap.Allocates before .integer (some (.integer value)) location middle := .append
    have allocate' : Dynamic.Heap.Allocates before binder.scheme.body (some (.integer value)) location middle := by
      rw [typed]; exact allocate
    obtain ⟨finalEnvironment, after, allocated, represented, cells, preserved⟩ :=
      ih ((binder.id, location) :: environment) middle
    refine ⟨finalEnvironment, after, .cons allocate' allocated, ?_, ?_, ?_⟩
    · intro id binding found
      rw [lookup_bind] at found
      split at found
      · rename_i same
        have sameBinding := Option.some.inj found
        cases sameBinding
        refine ⟨location, integerCell value, ?_, ?_, rfl, rfl⟩
        · exact same ▸ preserved binder.id (by simp) location .head
        · cases allocate.reads_new with
          | intro selected =>
            constructor
            rw [cells]
            exact selected.append_left
      · exact represented id binding found
    · simpa only [middle, List.map_cons, List.append_assoc, List.singleton_append] using cells
    · intro id member oldLocation found
      have different : binder.id ≠ id := by
        intro same
        exact fresh (same ▸ member)
      exact preserved id (by simp [member]) oldLocation (.tail different found)

/-- An accepted input environment has a source allocation from the empty
lexical environment and preserves every original heap cell. -/
theorem allocate {source : SourceInference.TypedSource}
    {binders : List SourceInference.TypedBinder} {values : List Int} {actual : Staged.Environment}
    (checked : Staged.Statements.InputsChecked source [] binders values actual)
    (before : Dynamic.Heap) :
    ∃ environment after,
      Dynamic.BindersAllocate [] before binders (values.map Dynamic.Value.integer) environment after ∧
      EnvironmentRep actual environment after ∧
      after.cells = before.cells ++ values.map integerCell := by
  obtain ⟨environment, after, allocated, represented, cells, _⟩ := allocate_seen checked [] before
  exact ⟨environment, after, allocated, represented, cells⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
open Frontend SourceInference SourceCoreElaboration SourceCoreElaboration.Internal
open SourceStagedClosedEvaluationMeaning

/-- Actual acceptance and independent source typing provide the required lexical
extensions. Execution appends only the Integer cells allocated by selected lets. -/
theorem statements_of_accepted
    {program : Program} {context finalTyped : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {solved : List SolvedRequirement} {actual : Staged.Environment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {fuel : Nat}
    {site : ErrorSite} {reason : ErrorReason} {roots : List StatementId}
    {result : StagedIntegerEvaluation} {control : ControlContext} {facts : BodyFacts}
    (accepted : Staged.Statements.evaluate solved source actual true fuel site reason roots = .ok result)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context roots finalTyped facts)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.Statements.Checked solved source actual true fuel roots result ∧
      ∃ final after added,
        Dynamic.StatementsExecute program context evidence source environment before roots final
          (.returned (.integer result.value)) after ∧ Extends before after added := by
  have checked := Staged.Statements.checked accepted
  exact ⟨checked, formed_meaning (bindingsFormed_of_typing checked unique typed) rfl ledger environments valid⟩

private theorem roots_filterMap {roots : List StatementId} {sourceRoots : List NodeId}
    (same : roots.map NodeId.statement = sourceRoots) :
    (sourceRoots.filterMap fun root => match root with
      | .statement statement => some statement | .expression _ => none) = roots := by
  subst sourceRoots
  induction roots with
  | nil => rfl
  | cons head tail ih => simpa using congrArg (List.cons head) ih

/-- The public reject-calls function evaluator supplies its full validation
receipt and a source execution from the actual ordered input allocation. The
whole original heap remains, followed by inputs and selected let allocations.
This statement does not identify those source-only cells with an erased runtime heap. -/
theorem evaluateStagedIntegerFunction_sound
    {function : CheckedFunction} {arguments : List Int} {value : Int}
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {before : Dynamic.Heap} {facts : BodyFacts}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value)
    (unique : NodeOccurrencesUnique function.typedBody)
    (typed : BodyHasType function.typedBody context .integer facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id))) :
    Staged.Statements.FunctionChecked function arguments value ∧
      ∃ environment bound roots final after added,
        roots.map NodeId.statement = function.typedBody.roots ∧
        Dynamic.BindersAllocate [] before function.typedBody.inputs
          (arguments.map Dynamic.Value.integer) environment bound ∧
        Dynamic.StatementsExecute program context evidence function.typedBody environment bound roots final
          (.returned (.integer value)) after ∧ Extends before after (arguments ++ added) := by
  have checked := Staged.Statements.function_checked accepted
  refine ⟨checked, ?_⟩
  cases checked with
  | intro owned arity inferred type inputs roots statements returned reconciled =>
      rename_i actual sourceRoots result
      obtain ⟨environment, bound, allocated, represented, inputCells⟩ := allocate inputs before
      obtain ⟨finalTyped, typed, rootKinds, completes⟩ := typed
      have typed' := (roots_filterMap roots) ▸ typed
      have formed := bindingsFormed_of_typing statements unique typed'
      have used : UsedValid context function.solvedRequirements result.consumedRequirements := by
        intro row proof member consumed actual
        exact valid row proof member (List.mem_map.mpr ⟨row, member, rfl⟩) actual
      obtain ⟨final, after, added, executed, cells⟩ := formed_meaning (program := program)
        (evidence := evidence) formed rfl ledger represented used
      refine ⟨environment, bound, _, final, after, added, roots, allocated, ?_, ?_⟩
      · simpa only [returned] using executed
      · exact (show Extends before bound arguments from inputCells).trans cells

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning
