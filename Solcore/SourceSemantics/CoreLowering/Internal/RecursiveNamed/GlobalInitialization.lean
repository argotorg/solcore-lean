import Solcore.SourceSemantics.CoreLowering.FunctionCallBody
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreLambdaTemplates
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
import Solcore.Core.Correspondence
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize

/-!
# Recursive named rows: global initialization

Meaning and typing of the initialization of global function slots, the initial context, and the Source of named calls and their arguments.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCallSource
/-! Exact source declarations at a concrete named body.  Structural source
instantiation and evidence are independent of native code authentication.
The body outcome is the existing declarative relation, not a semantic field in
a compiler certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls
open Frontend SourceInference

structure SourceFrame (program : Program) (instantiation : DeclarationInstantiation)
    (bodyInstance : Dynamic.BodyInstance) (function : Dynamic.Closure) : Prop where
  instantiated : Dynamic.FunctionInstantiates program instantiation bodyInstance
  source : function.source = bodyInstance.source
  context : function.context = bodyInstance.context
  parameters : function.parameters = bodyInstance.source.inputs
  result : function.resultType = bodyInstance.resultType
  captured : function.captured = []
  roots : Dynamic.StatementRoots bodyInstance.source.roots function.body
  covers : function.evidence.Covers bodyInstance.context

inductive BodyOutcome (program : Program) (bodyInstance : Dynamic.BodyInstance)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (arguments : List Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {result after} (execution : Dynamic.BodyInvokes program bodyInstance evidence before arguments result after) :
      BodyOutcome program bodyInstance evidence before arguments (.value result) after
  | fault {reason after} (execution : Dynamic.BodyFaults program bodyInstance evidence before arguments reason after) :
      BodyOutcome program bodyInstance evidence before arguments (.fault reason) after

variable {program : Program} {instantiation : DeclarationInstantiation}
  {bodyInstance : Dynamic.BodyInstance} {function : Dynamic.Closure}

theorem SourceFrame.call {callerContext : SourceSemantics.Context}
    {caller : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (frame : SourceFrame program instantiation bodyInstance function)
    (execution : BodyOutcome program bodyInstance function.evidence before arguments outcome after) :
    FunctionCallBody.Outcome program callerContext caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after := by
  cases execution with
  | value executed => exact .value (.global frame.instantiated rfl frame.covers executed)
  | fault executed => exact .fault (.globalBody frame.instantiated rfl executed)

/-- The real named source body is a closure-shaped trace only as a proof
view. It retains the exact declaration bodyInstance and allocates from the empty
lexical frame; no lambda occurrence is fabricated. -/
theorem SourceFrame.body_of_trace {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {environment : Dynamic.Environment} {outcome : Dynamic.ExpressionOutcome}
    (frame : SourceFrame program instantiation bodyInstance function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    BodyOutcome program bodyInstance function.evidence before arguments outcome after := by
  have extension : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs types context := by
    simpa only [frame.source, frame.context, frame.parameters] using extended
  have allocation : Dynamic.BindersAllocate [] before bodyInstance.source.inputs arguments environment bound :=
    frame.parameters ▸ allocated
  cases trace with
  | returned executed =>
      exact .value (.returned frame.covers frame.roots extension allocation (frame.source ▸ executed) rfl)
  | unit same executed =>
      exact .value (.unit frame.covers (frame.result ▸ same) frame.roots extension allocation
        (frame.source ▸ executed) ⟨_, rfl⟩)
  | fault failed =>
      exact .fault (.statements frame.roots extension allocation (frame.source ▸ failed))
  | escaped executed escape =>
      exact .fault (.controlEscape frame.roots extension allocation (frame.source ▸ executed) escape)

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Invert the independent body invocation at the statically retained call
context. Exact roots and monomorphic binder extension identify that context;
arity excludes the separate source arity-fault rule. -/
theorem SourceFrame.trace_of_body {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (frame : SourceFrame program instantiation bodyInstance function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program bodyInstance function.evidence before arguments outcome after) :
    ∃ environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after := by
  have rootsUnique : ∀ {roots}, Dynamic.StatementRoots bodyInstance.source.roots roots → roots = function.body := by
    intro roots selected
    exact roots_functional selected frame.roots
  have contextUnique : ∀ {inputTypes actualContext},
      MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs inputTypes actualContext →
      actualContext = context := by
    intro inputTypes actualContext extension
    have actual : MonoBindersExtend function.source.owner function.context function.parameters inputTypes actualContext := by
      simpa only [frame.source, frame.context, frame.parameters] using extension
    have same : types = inputTypes := extended.bodyTypes_eq.symm.trans actual.bodyTypes_eq
    subst inputTypes
    exact (extended.functional actual).symm
  cases executed with
  | value invokes =>
    cases invokes with
    | returned covers roots extension allocated execution returned =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .returned (frame.source.symm ▸ execution)⟩
    | unit covers same roots extension allocated execution fellThrough =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      obtain ⟨_, rfl⟩ := fellThrough
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .unit (frame.result.symm ▸ same) (frame.source.symm ▸ execution)⟩
  | fault fails =>
    cases fails with
    | arity mismatch => exact False.elim (mismatch (by simpa only [frame.parameters] using arity))
    | statements roots extension allocated failed =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .fault (frame.source.symm ▸ failed)⟩
    | controlEscape roots extension allocated executed escape =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .escaped (frame.source.symm ▸ executed) escape⟩

/-- The closed nil-argument direct-call expression uses precisely the source
declaration/evidence selected by its occurrence metadata. -/
theorem direct_nil {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {node calleeNode : ExpressionNode} {name : String}
    {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee [] (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates invocation)
    (called : FunctionCallBody.Outcome program context evidence invocation before
      (.global ⟨instantiation, invocation⟩) [] outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases called with
  | value applies =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
    · rw [form]
      exact .directCall (lookupExpression?_sound calleeFound) calleeForm calleeRequirements calleeCoercions
        valid .nil closed applies
    · rw [coercions]; exact .nil
  | fault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound found)
    rw [form]
    exact .directApply .nil closed failed

/-- A declaration reference produces the exact source instantiation and its
closed evidence. Native global authentication is deliberately separate. -/
theorem reference {context : SourceSemantics.Context} {evidence produced : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (coercions : node.coercions = [])
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.RequirementsProduceEnvironment context evidence [] instantiation.predicates produced) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id
      (.global ⟨instantiation, produced⟩) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
  · rw [form]
    exact .declaration layout valid closed
  · rw [coercions]
    exact .nil

end Solcore.SourceSemantics.CoreLowering.NamedCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCallArgumentSource
/-! Direct named-call outcomes retain the independently instantiated source
body. Arguments run before that body, and a first argument fault skips it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
open Frontend SourceInference

inductive Trace (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (ids : List ExpressionId)
    (body : Dynamic.BodyInstance) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentFault {reason after}
      (failed : Dynamic.ExpressionsFault program context caller source environment before ids reason after) :
      Trace program context caller invocation source environment before ids body (.fault reason) after
  | apply {arguments middle outcome after}
      (evaluated : Dynamic.ExpressionsEvaluate program context caller source environment before ids arguments middle)
      (applied : NamedCalls.BodyOutcome program body invocation middle arguments outcome after) :
      Trace program context caller invocation source environment before ids body outcome after

/-- Build the actual independent direct-call occurrence, retaining its exact
callee metadata and source evidence. No compiler type selects a source body. -/
theorem expression {program : Program} {context : SourceSemantics.Context}
    {caller : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {outcome : Dynamic.ExpressionOutcome}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.DirectCallProducesEvidence context caller node.requirements node.coercions instantiation.predicates function.evidence)
    (trace : Trace program context caller function.evidence source environment before ids body outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context caller source environment before id outcome after := by
  cases trace with
  | argumentFault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound found)
    rw [form]
    exact .directArguments (lookupExpression?_sound calleeFound) calleeForm failed
  | apply evaluated applied =>
    have invoked := frame.call (callerContext := context) (caller := caller) applied
    cases invoked with
    | value applies =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
      · rw [form]
        exact .directCall (lookupExpression?_sound calleeFound) calleeForm calleeRequirements calleeCoercions
          valid evaluated closed applies
      · rw [coercions]; exact .nil
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound found)
      rw [form]
      exact .directApply evaluated closed failed

end Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
/-! Initial named source contexts are derived before constructing a catalog
Header. The actual frame and parameter extension retain scoped requirements
and evidence coverage. Full ledger validity is obtained only under an explicit
empty-template check on the complete source; unused rows are never removed.
No runtime trace, native typing or Header.valid is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
open Frontend SourceInference

/-- Parameter installation changes only lexical fields, retaining the same
signature catalog, assumptions, complete ledger and residual-variable mode. -/
theorem mono_fields {owner : Resolved.DeclarationId} {initial final : Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner initial parameters types final) :
    Dynamic.RuntimeContextFields initial final := by
  induction extended with
  | nil => exact .refl _
  | cons _ head _ ih => exact (Dynamic.RuntimeContextFields.ofBinderExtends head).trans ih

variable {program : Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {context : Context} {types : List TypeSystem.Ty}

/-- Independent program validity supplies the whole scoped ledger. Its source
identity and actual parameter context are fixed by the real frame. -/
theorem scoped_ledger (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) :
    ScopedRequirementLedgerWellFormed context function.source := by
  obtain ⟨_, _, _, certificate⟩ := frame.instantiated.certificate programTyped
  have original : ScopedRequirementLedgerWellFormed function.context function.source := by
    simpa only [frame.context, frame.source] using certificate.requirement_ledger
  exact (mono_fields extended).scopedRequirementLedger original

/-- Execution-facing ledger validity keeps every row, including assumption
and qualified template rows. It is not full ordinary ledger validity. -/
theorem runtime (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) :
    RuntimeRequirementLedgerValid context :=
  (scoped_ledger frame extended programTyped).toRuntime

/-- The same frame dictionary covers the actual installed parameter context.
Neither equality with another dictionary nor evidence uniqueness is needed. -/
theorem covers (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context) :
    function.evidence.Covers context := by
  apply (mono_fields extended).covers
  simpa only [frame.context] using frame.covers

/-- A check of the complete retained source, including unused nodes, removes
only the template alternative in scoped validity. No ledger row is dropped. -/
theorem ordinary {source : TypedSource}
    (ledger : ScopedRequirementLedgerWellFormed context source)
    (templatesEmpty : source.localSchemeTemplateIds = []) :
    RequirementLedgerWellFormed context := by
  refine ⟨ledger.idsUnique, ?_⟩
  intro row member
  exact ledger.ordinary_valid member (by
    simp only [← typedSourceLocalSchemeTemplateIds_eq_carrier, templatesEmpty, List.not_mem_nil, not_false_eq_true])

/-- This bounded entry constructs the existing semantic context condition
without a Header or prior context-validity callback. Template-bearing sources
remain outside this conversion even when their templates are unreachable. -/
theorem of_templates_empty (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) {solved : List SolvedRequirement}
    (sameLedger : function.context.solvedRequirements = solved)
    (templatesEmpty : function.source.localSchemeTemplateIds = []) :
    CompatibleExpressionLiterals.ContextValid solved context function.evidence :=
  ⟨(mono_fields extended).solvedRequirements.trans sameLedger,
    ordinary (scoped_ledger frame extended programTyped) templatesEmpty, covers frame extended⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
/-! Actual global reservations and cached lambda installation are finite Core
prefixes. Their exact physical references, closure code and captured Unit
binders are derived from emitted syntax, independently of source body meaning.
The continuation law is explicit in general composition. Source attribution,
initial frame history, represented heaps and catalog Authority remain separate.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
open Core Frontend
abbrev Signature := SourceCoreCalls.Signature

/-- Pure layout of the emitted reservations, in actual allocation order. -/
def reserve (signatures : List Signature) (store : Store) (environment : Environment) : Store × Environment :=
  match signatures with
  | [] => (store, environment)
  | signature :: rest => reserve rest (store ++ [.inLeft signature.functionType .unit])
      (.cellRef (OptionalCell.cellType signature.functionType) store.length :: environment)

theorem reserved_store (signatures : List Signature) (store : Store) (environment : Environment) :
    (reserve signatures store environment).1 = store ++ signatures.map (fun signature => .inLeft signature.functionType .unit) := by
  induction signatures generalizing store environment with
  | nil => simp [reserve]
  | cons signature rest ih =>
    simp only [reserve, ih, List.map_cons, List.append_assoc, List.singleton_append]

/-- The actual reversed environment retains each reservation's allocation
location and full optional function-cell type. -/
theorem reserved_environment (signatures : List Signature) (store : Store) (environment : Environment) :
    (reserve signatures store environment).2 =
      ((signatures.zipIdx store.length).map (fun (signature, location) =>
        Value.cellRef (OptionalCell.cellType signature.functionType) location)).reverse ++ environment := by
  induction signatures generalizing store environment with
  | nil => simp [reserve]
  | cons signature rest ih =>
    simp only [reserve, ih, List.length_append, List.length_singleton,
      List.zipIdx_cons, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem reserved_prefix (signatures : List Signature) (store : Store) (environment : Environment)
    {location : Nat} (earlier : location < store.length) :
    (reserve signatures store environment).1.read? location = store.read? location := by
  rw [reserved_store]
  exact List.getElem?_append_left earlier

/-- A row in the actual newest-first global inventory determines its physical
reference; no environment lookup or allocation bound is an assumed law. -/
theorem reserved_reference (signatures : List Signature) (store : Store) (environment : Environment)
    {index : Nat} {signature : Signature} (found : signatures.reverse[index]? = some signature) :
    (reserve signatures store environment).2[index]? = some
      (.cellRef (OptionalCell.cellType signature.functionType) (store.length + (signatures.length - 1 - index))) := by
  have within : index < signatures.length := by
    obtain ⟨valid, _⟩ := List.getElem?_eq_some_iff.mp found
    simpa using valid
  rw [reserved_environment, List.getElem?_append_left (by simpa using within)]
  rw [List.getElem?_reverse (by simpa using within)]
  simp only [List.length_map, List.length_zipIdx, List.getElem?_map, List.getElem?_zipIdx]
  rw [List.getElem?_reverse (by simpa using within)] at found
  rw [found]
  rfl

theorem reserved_location_bound (signatures : List Signature) (store : Store) (environment : Environment)
    {index : Nat} (within : index < signatures.length) :
    store.length + (signatures.length - 1 - index) < (reserve signatures store environment).1.length := by
  rw [reserved_store]
  simp only [List.length_append, List.length_map]
  omega

/-- The original allocation prefix has exactly the same child evaluation,
with no execution of a source expression or a function body. -/
theorem allocated_iff (signatures : List Signature) (body : Expr)
    (environment : Environment) (store finalStore : Store) (value : Value) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals signatures body) value finalStore ↔
    Evaluates (reserve signatures store environment).2 (reserve signatures store environment).1 body value finalStore := by
  induction signatures generalizing environment store with
  | nil => rfl
  | cons signature rest ih =>
    change Evaluates environment store (.letE (OptionalCell.allocate signature.functionType)
      (SourceCoreRecursiveEntry.allocateGlobals rest body)) value finalStore ↔ _
    constructor
    · intro completed
      cases completed with
      | letE allocated tail =>
        cases allocated with
        | newCell initialized =>
          cases initialized with
          | inLeft payload =>
            cases payload
            exact (ih _ _).mp tail
    · intro completed
      exact .letE (.newCell (.inLeft .unit)) ((ih _ _).mpr completed)

/-- A syntactic cached lambda row; it contains no execution law. -/
structure LambdaRow where
  parameter : Ty
  result : Ty
  body : Expr

def LambdaRow.expression (row : LambdaRow) : Expr := .lambda row.parameter row.result row.body

def shift (count : Nat) : Renaming := fun index => index + count

def shifted (count : Nat) (expression : Expr) : Expr := expression.rename (shift count)

private theorem shifted_weaken (count : Nat) (expression : Expr) :
    (expression.weakenAt 0).rename (shift count).lift = shifted (count + 1) expression := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  apply congrArg (Expr.rename expression)
  funext index
  simp [Renaming.comp, Renaming.insertion, Renaming.lift, shift, Nat.add_assoc]

private theorem shifted_front (count : Nat) (expression : Expr) :
    (shifted count expression).weakenAt 0 = shifted (count + 1) expression := by
  unfold shifted
  rw [← Expr.rename_insertion, Expr.rename_comp]
  apply congrArg (Expr.rename expression)
  funext index
  simp [Renaming.comp, Renaming.insertion, shift, Nat.add_assoc]

theorem installed_template (count : Nat) (expression : Expr) :
    SourceCoreLambdaTemplates.installedTemplate count expression = shifted count expression := by
  induction count with
  | zero =>
    have same : shift 0 = Renaming.id := by funext index; simp [shift, Renaming.id]
    simp [SourceCoreLambdaTemplates.installedTemplate, shifted, same]
  | succ count ih =>
    rw [SourceCoreLambdaTemplates.installedTemplate, List.range_succ, List.foldl_append]
    change (SourceCoreLambdaTemplates.installedTemplate count expression).weakenAt 0 = _
    rw [ih, shifted_front]

/-- Exact captured code includes every prior installer Unit binder. -/
def installedValue (environment : Environment) (index : Nat) (row : LambdaRow) : Value :=
  .closure row.parameter row.result (row.body.rename (shift index).lift)
    (List.replicate index .unit ++ environment)

private def installItems (rows : List LambdaRow) (index : Nat) (body : Expr) : Expr :=
  (rows.zipIdx index).foldr (fun (row, slot) continuation =>
    .letE (.storeCell (.var slot) (.inRight .unit row.expression)) (continuation.weakenAt 0)) body

private theorem installItems_actual (rows : List LambdaRow) (body : Expr) :
    installItems rows 0 body = SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) body := by
  simp only [installItems, SourceCoreRecursiveEntry.installFunctions, List.zipIdx_map, List.foldr_map, Prod.map, id]

def installStore (rows : List LambdaRow) (locations : Nat → Location) (environment : Environment)
    (store : Store) (index : Nat) : Store :=
  match rows with
  | [] => store
  | row :: rest => installStore rest locations environment
      (store.set (locations index) (.inRight .unit (installedValue environment index row))) (index + 1)

theorem installed_length (rows : List LambdaRow) (locations : Nat → Location)
    (environment : Environment) (store : Store) (index : Nat) :
    (installStore rows locations environment store index).length = store.length := by
  induction rows generalizing store index with
  | nil => rfl
  | cons row rest ih => simp only [installStore, ih, List.length_set]

private theorem shifted_install_iff (rows : List LambdaRow) (body : Expr)
    (environment : Environment) (store finalStore : Store) (locations : Nat → Location) (index : Nat) (value : Value)
    (references : ∀ i row, rows[i]? = some row → environment[index + i]? =
      some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations (index + i))))
    (bounds : ∀ i, i < rows.length → locations (index + i) < store.length) :
    Evaluates (List.replicate index .unit ++ environment) store (shifted index (installItems rows index body)) value finalStore ↔
    Evaluates (List.replicate (index + rows.length) .unit ++ environment)
      (installStore rows locations environment store index) (shifted (index + rows.length) body) value finalStore := by
  induction rows generalizing store index with
  | nil => simp only [installItems, List.zipIdx_nil, List.foldr_nil, List.length_nil, Nat.add_zero, installStore]
  | cons row rest ih =>
    have reference : (List.replicate index .unit ++ environment)[index + index]? =
        some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations index)) := by
      rw [List.getElem?_append_right (by simp)]
      simpa using references 0 row rfl
    have bound : locations index < store.length := by simpa using bounds 0 (by simp)
    obtain ⟨old, read⟩ : ∃ old, store.read? (locations index) = some old := by
      exact ⟨store[locations index], List.getElem?_eq_getElem bound⟩
    let nextStore := store.set (locations index) (.inRight .unit (installedValue environment index row))
    have written : store.write? (locations index) (.inRight .unit (installedValue environment index row)) = some nextStore :=
      Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩
    have write : Evaluates (List.replicate index .unit ++ environment) store
        (shifted index (.storeCell (.var index) (.inRight .unit row.expression))) .unit nextStore := by
      exact .storeCell (.var reference) read (.inRight .lambda) written
    have tailReferences : ∀ i selected, rest[i]? = some selected → environment[index + 1 + i]? =
        some (.cellRef (OptionalCell.cellType (.function selected.parameter selected.result)) (locations (index + 1 + i))) := by
      intro i selected found
      have selected := references (i + 1) selected found
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using selected
    have tailBounds : ∀ i, i < rest.length → locations (index + 1 + i) < nextStore.length := by
      intro i within
      have valid := bounds (i + 1) (by simpa using Nat.succ_lt_succ within)
      simpa only [nextStore, List.length_set, Nat.add_assoc, Nat.add_comm 1 i] using valid
    have tail := ih nextStore (index + 1) tailReferences tailBounds
    have length : index + (row :: rest).length = index + 1 + rest.length := by simp; omega
    rw [length]
    change Evaluates _ _ (.letE _ (((installItems rest (index + 1) body).weakenAt 0).rename (shift index).lift)) _ _ ↔ _
    rw [shifted_weaken]
    constructor
    · intro completed
      cases completed with
      | letE actual tailCompleted =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic actual write
        exact tail.mp (by simpa only [List.replicate_succ, List.cons_append] using tailCompleted)
    · intro completed
      exact .letE write (by simpa only [List.replicate_succ, List.cons_append] using tail.mpr completed)

/-- Actual installation introduces only its real Unit binders and store
writes. The continuation is the same emitted body under those binders. -/
theorem installed_iff (rows : List LambdaRow) (body : Expr)
    (environment : Environment) (store finalStore : Store) (locations : Nat → Location) (value : Value)
    (references : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → environment[i]? =
      some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations i)))
    (bounds : ∀ i, i < rows.length → locations i < store.length) :
    Evaluates environment store (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) body) value finalStore ↔
    Evaluates (List.replicate rows.length .unit ++ environment)
      (installStore rows locations environment store 0) (shifted rows.length body) value finalStore := by
  have meaning := shifted_install_iff rows body environment store finalStore locations 0 value (by simpa using references) (by simpa using bounds)
  have same : shift 0 = Renaming.id := by funext index; simp [shift, Renaming.id]
  simpa [shifted, same, installItems_actual] using meaning

/-- No write targets a protected location. This is derived from the real
ordered installer state, without treating closure typing as read authority. -/
theorem installed_preserves_other (rows : List LambdaRow) (locations : Nat → Location)
    (environment : Environment) (store : Store) (index location : Nat)
    (different : ∀ i, i < rows.length → locations (index + i) ≠ location) :
    (installStore rows locations environment store index).read? location = store.read? location := by
  induction rows generalizing store index with
  | nil => rfl
  | cons row rest ih =>
    rw [installStore, ih]
    · exact List.getElem?_set_ne (by simpa using different 0 (by simp))
    · intro i within
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using different (i + 1) (by simpa using Nat.succ_lt_succ within)

/-- Each final read retains this row's full installed code and actual captured
environment. Distinctness is required only for real occupied slots. -/
theorem installed_read (rows : List LambdaRow) (locations : Nat → Location)
    (environment : Environment) (store : Store) (index : Nat)
    (bounds : ∀ i, i < rows.length → locations (index + i) < store.length)
    (distinct : ∀ i j, i < rows.length → j < rows.length → i ≠ j → locations (index + i) ≠ locations (index + j))
    {i : Nat} {row : LambdaRow} (found : rows[i]? = some row) :
    (installStore rows locations environment store index).read? (locations (index + i)) =
      some (.inRight .unit (installedValue environment (index + i) row)) := by
  induction rows generalizing store index i with
  | nil => simp at found
  | cons first rest ih =>
    cases i with
    | zero =>
      cases found
      rw [installStore, installed_preserves_other]
      · exact List.getElem?_set_self (by simpa using bounds 0 (by simp))
      · intro j within
        have diff := distinct (j + 1) 0 (by simpa using Nat.succ_lt_succ within) (by simp) (by omega)
        simpa only [Nat.add_assoc, Nat.add_zero, Nat.add_comm 1 j] using diff
    | succ i =>
      have nextBounds : ∀ j, j < rest.length → locations (index + 1 + j) <
          (store.set (locations index) (.inRight .unit (installedValue environment index first))).length := by
        intro j within
        simpa only [List.length_set, Nat.add_assoc, Nat.add_comm 1 j] using bounds (j + 1) (by simpa using Nat.succ_lt_succ within)
      have nextDistinct : ∀ j k, j < rest.length → k < rest.length → j ≠ k →
          locations (index + 1 + j) ≠ locations (index + 1 + k) := by
        intro j k hj hk ne
        have diff := distinct (j + 1) (k + 1) (by simpa using Nat.succ_lt_succ hj) (by simpa using Nat.succ_lt_succ hk) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm 1 k] using diff
      simpa only [installStore, Nat.add_assoc, Nat.add_comm 1 i] using
        ih (store.set (locations index) (.inRight .unit (installedValue environment index first))) (index + 1) nextBounds nextDistinct found

/-- Reservations append cells and every installation write is beyond the
old store. The complete old prefix survives, including any protocol frame. -/
theorem initialized_prefix (signatures : List Signature) (rows : List LambdaRow)
    (environment : Environment) (store : Store) (locations : Nat → Location)
    (later : ∀ i, i < rows.length → store.length ≤ locations i)
    {location : Nat} (earlier : location < store.length) :
    (installStore rows locations (reserve signatures store environment).2
      (reserve signatures store environment).1 0).read? location = store.read? location := by
  have unchanged := installed_preserves_other rows locations (reserve signatures store environment).2
    (reserve signatures store environment).1 0 location (by
      intro i within
      have beyond := later i within
      simpa only [Nat.zero_add] using (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le earlier beyond))))
  exact unchanged.trans (reserved_prefix signatures store environment earlier)

/-- The actual bootstrap continuation is closed here. It does not call any
cached function body. Its successful result leaves every installed slot intact. -/
theorem bootstrap_evaluates (signatures : List Signature) (rows : List LambdaRow)
    (environment : Environment) (store : Store) (locations : Nat → Location)
    (references : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row →
      (reserve signatures store environment).2[i]? =
        some (.cellRef (OptionalCell.cellType (.function row.parameter row.result)) (locations i)))
    (bounds : ∀ i, i < rows.length → locations i < (reserve signatures store environment).1.length) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals signatures
      (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows locations (reserve signatures store environment).2 (reserve signatures store environment).1 0) := by
  apply (allocated_iff signatures _ environment store _ _).mpr
  apply (installed_iff rows _ _ _ _ locations _ references bounds).mpr
  exact .inRight .unit

/-- A static, ordered cache-to-signature receipt supplies the only remaining
installation premise. Every physical reference and allocation bound follows
from the actual reservation prefix. This receipt carries no body meaning. -/
theorem ordered_bootstrap_evaluates (signatures : List Signature) (rows : List LambdaRow)
    (environment : Environment) (store : Store)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures.reverse[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    Evaluates environment store (SourceCoreRecursiveEntry.allocateGlobals signatures
      (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) (LanguageResult.success .unit)))
      (.inRight .word .unit)
      (installStore rows (fun index => store.length + (signatures.length - 1 - index))
        (reserve signatures store environment).2 (reserve signatures store environment).1 0) := by
  apply bootstrap_evaluates
  · intro i row found
    obtain ⟨signature, selected, same⟩ := ordered i row found
    simpa only [same] using reserved_reference signatures store environment selected
  · intro i within
    have found : rows[i]? = some rows[i] := List.getElem?_eq_getElem within
    obtain ⟨signature, selected, _⟩ := ordered i rows[i] found
    obtain ⟨valid, _⟩ := List.getElem?_eq_some_iff.mp selected
    exact reserved_location_bound signatures store environment (by simpa using valid)

end Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationTyping
/-! The real recipe supplies native typing for its actual bootstrap. Combining
that static receipt with the closed initialization trace gives typed stored
closures and their actual captured environments. Source attribution, heaps and
execution history are constructed separately; runtime type tags do not supply
them. No source function body is evaluated in this module. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationTyping
open Core Frontend
open RecursiveGlobalInitializationMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- Accepted preparation owns this exact compiled program and this actual
frame/global/cache expression, before any runtime execution. -/
theorem recipe_emitted {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe) :
    recipe.compiled = compiled ∧ recipe.bootstrap =
      SourceCoreCallableIndexedFrames.allocate compiled.indexed.ancestry.layout.frame
        (SourceCoreRecursiveEntry.allocateGlobals compiled.indexed.base.globals.reverse
          (SourceCoreRecursiveEntry.installFunctions compiled.indexed.secondPass.closures (LanguageResult.success .unit))) := by
  unfold SourceCoreIndexedSession.Recipe.prepare at accepted
  obtain ⟨roots, _, accepted⟩ := bind_ok accepted
  obtain ⟨templates, _, accepted⟩ := bind_ok accepted
  obtain ⟨named, _, accepted⟩ := bind_ok accepted
  obtain ⟨builtins, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl⟩
  · cases accepted

def initialEnvironment (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout) : Environment :=
  (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).2

def initialStore (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout) : Store :=
  installStore rows (fun index => 1 + (signatures.length - 1 - index))
    (initialEnvironment signatures layout)
    (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).1 0

/-- Frame allocation is part of the actual original native trace. The history
attached to its empty value is established later from the empty constructor. -/
theorem framed_bootstrap (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    Evaluates [] [] (SourceCoreCallableIndexedFrames.allocate layout
      (SourceCoreRecursiveEntry.allocateGlobals signatures.reverse
        (SourceCoreRecursiveEntry.installFunctions (rows.map LambdaRow.expression) (LanguageResult.success .unit))))
      (.inRight .word .unit) (initialStore signatures rows layout) := by
  refine .letE (.newCell (CallableIndexedContextFrames.literal_evaluates layout .empty [] [])) ?_
  simpa only [initialStore, initialEnvironment, List.length_singleton, List.length_nil, List.nil_append,
    List.reverse_reverse, List.length_reverse] using
    ordered_bootstrap_evaluates signatures.reverse rows [.cellRef layout.type 0]
      [SourceCoreCallableIndexedFrames.encode layout .empty] (by simpa using ordered)

theorem stored {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (rows : List LambdaRow) (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result) :
    ∃ world, RuntimeStoreHasTypes world
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)
      compiled.indexed.layouts.definitions := by
  obtain ⟨owned, emitted⟩ := recipe_emitted accepted
  have typed := recipe.bootstrapTyped
  rw [emitted, owned, cached] at typed
  obtain ⟨world, _, stored, _⟩ := evaluation_preserves_type
    (framed_bootstrap compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame ordered)
    typed .nil (.nil compiled.indexed.layouts.definitions)
  exact ⟨world, stored⟩

/-- This inversion concerns the full stored closure, including its exact
renamed code and captured values. It does not reconstruct source identity. -/
theorem stored_closure {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typed : RuntimeStoreHasTypes world store definitions)
    {location : Location} {parameter result : Ty} {body : Expr} {captured : Environment}
    (read : store.read? location = some (.inRight .unit (.closure parameter result body captured))) :
    ∃ context, RuntimeEnvironmentHasTypes world captured context definitions ∧
      HasType (parameter :: context) body result definitions := by
  change store[location]? = some (.inRight .unit (.closure parameter result body captured)) at read
  have found : world[location]? = some (.sum .unit (.function parameter result)) := by
    rw [typed.world_eq, List.getElem?_map, read]
    rfl
  obtain ⟨value, actual, related⟩ := typed.lookup found
  have same := Option.some.inj (actual.symm.trans read)
  subst value
  cases related with
  | inRight closure =>
    cases closure with
    | closure environment code => exact ⟨_, environment, code⟩

/-- Removing the real installer Unit prefix only exposes the original
canonical environment. No captured values or closure code are changed. -/
theorem drop_installer_units {definitions : DataEnvironment} {world : StoreTyping} {environment : Environment}
    {context : Core.Context} (count : Nat)
    (typed : RuntimeEnvironmentHasTypes world (List.replicate count .unit ++ environment) context definitions) :
    ∃ canonicalContext, RuntimeEnvironmentHasTypes world environment canonicalContext definitions := by
  induction count generalizing context with
  | zero => exact ⟨_, typed⟩
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append] at typed
    cases typed with
    | cons _ tail => exact ih tail

end Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedArgumentFaultPostContracts
/-! A named argument failure keeps its genuine parent and callee occurrences.
The finite join uses the same failed list and reached semantic tuple. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedArgumentFaultPostContracts
open Core Frontend SourceInference GeneralHeap ExpressionFailurePostContracts

structure ArgumentsJoin (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) : Prop where
  arguments : ∀ {id callee : ExpressionId} {ids : List ExpressionId} {node calleeNode : ExpressionNode}
    {instantiation : DeclarationInstantiation} {name : String}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {mapping : LocationMap} {world : StoreTyping} {store : Store},
    ContainsExpression source id node → node.form = .call callee ids (.declaration instantiation) →
    ContainsExpression source callee calleeNode →
    calleeNode.form = .reference name (.declaration instantiation) →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    expressionPost program context evidence source environment before id reason after token mapping world store

/-- Only the two original Source constructors are used. The sized list proof
is retained directly, without measuring or searching its failure again. -/
theorem source_fault {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {id callee : ExpressionId} {ids : List ExpressionId} {node calleeNode : ExpressionNode}
    {instantiation : DeclarationInstantiation} {name : String}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {size : Nat}
    (parent : ContainsExpression source id node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeContains : ContainsExpression source callee calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (failed : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) :
    SourceExecutionSize.ExpressionFaults program
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]])
      context evidence source environment before id reason after := by
  exact .form parent (form ▸ .directArguments calleeContains calleeForm failed)

end Solcore.SourceSemantics.CoreLowering.NamedArgumentFaultPostContracts
end
