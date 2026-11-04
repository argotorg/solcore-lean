import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.AcceptedTrees
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedCallFaults
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation

/-!
# Cell-aware named bodies: expression certificates

Certificates, syntax, policies and collectors of named expressions, with the diagnostics of reads and indices and the issuer that supplies them.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
/-! The actual named preparation retains its diagnostic inventory and callback.
Every generalized initializer receives that same issuer before it is allocated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
open Core Frontend SourceInference

variable {whole : SourceCoreUnifiedCompilation.Compiled}

def Named (prepared : SourceCoreCallableIndexedPrograms.Prepared whole.compatible.checked)
    (named : SourceCoreGeneralFunctions.Function) (reasonAt : ExpressionId → Word) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial whole.compatible.checked),
    prepared.base.diagnostics = some issued ∧
    reasonAt = issued.program.reasonAt named.signature.key ∧
    ∃ own : SourceCoreProgramFaultSites.Function,
      issued.program.base.find? named.signature.key = some own

theorem Named.initializer {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
    {reasonAt : ExpressionId → Word} (issuer : Named whole.indexed named reasonAt)
    (rootFuel budget : Nat) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) :
    GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
      (GeneralizedLocalInitializerCompilation.namedInputs compiled rootFuel budget
        (CallableIndexedNamedGeneration.context whole.indexed named) scope id reasonAt) := issuer

theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    Named whole.indexed header.named header.reasonAt := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have sameBase : prepared.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases whole.indexed.base.callableContext <;> rfl
  have ownFound := prepared.compilation.diagnostic
  rw [sameBase] at ownFound
  refine ⟨issued, present, ?_, prepared.compilation.own, ?_⟩
  · rw [aligned.reasonAt, aligned.named, lowered]
    cases whole.indexed.base.callableContext <;> rfl
  · simpa only [aligned.named] using ownFound

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedInitializerProfiles
/-! Finite initializer profiles inspect the actual catalog before execution.
Scope and compilation budgets do not change these original metadata checks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedInitializerProfiles
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open CallableIndexedNamedGeneration (Prepared Compilation context source)
open GeneralizedLocalInitializerCompilation (namedInputs)
open GeneralizedLocalInitializerPackets (Profile BindingProfile)

private theorem binding_member {locals : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} (located : locals.binding caller binder = .ok binding) : binding ∈ locals.bindings := by
  unfold Catalog.binding at located
  generalize filtered : locals.bindings.filter (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | nil =>
      cases located
      exact (List.mem_filter.mp (show binding ∈ locals.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by rw [filtered]; simp)).1
    | cons next tail => cases located

variable {checked : SourceCoreCompatibleCatalog.Checked}

structure Candidate (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (binding : Binding) (candidate : Instance) where
  original : GeneralizedLocalInitializerPackets.BindingObservations
    ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
    named.signature.key binding.initializer binding candidate
  body : GeneralizedLocalBodyProfile.Profile prepared.base.locals named.signature.key
    candidate.source binding.initializer

def candidates? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (binding : Binding) : (candidates : List Instance) →
      Option (PLift (∀ candidate ∈ candidates, Nonempty (Candidate prepared named binding candidate)))
  | [] => some ⟨by intro candidate member; cases member⟩
  | candidate :: rest => do
    let head ← GeneralizedLocalInitializerPackets.bindingObservations?
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      named.signature.key binding.initializer binding candidate
    let body ← GeneralizedLocalBodyProfile.profile? prepared.base.locals named.signature.key
      candidate.source binding.initializer
    let ⟨tail⟩ ← candidates? prepared named binding rest
    pure ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact ⟨⟨head, body⟩⟩
      · exact tail selected member⟩

def Rows (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (bindings : List Binding) : Prop :=
  ∀ binding ∈ bindings, binding.caller = named.signature.key →
    ∀ candidate ∈ binding.atContext [], Nonempty (Candidate prepared named binding candidate)

def rows? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) :
    (bindings : List Binding) → Option (PLift (Rows prepared named bindings))
  | [] => some ⟨by intro binding member; cases member⟩
  | binding :: rest => do
    let ⟨tail⟩ ← rows? prepared named rest
    if caller : binding.caller = named.signature.key then
      let ⟨head⟩ ← candidates? prepared named binding (binding.atContext [])
      pure ⟨by
        intro selected member owner
        rcases List.mem_cons.mp member with same | member
        · subst selected; exact head
        · exact tail selected member owner⟩
    else
      pure ⟨by
        intro selected member owner
        rcases List.mem_cons.mp member with same | member
        · subst selected; exact False.elim (caller owner)
        · exact tail selected member owner⟩

/-- The actual reached site selects its original finite catalog entry. No
identity is inferred from the row's native type. -/
theorem Rows.at_site {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (reasonAt : ExpressionId → Word)
    (profiles : Rows prepared named prepared.base.locals.bindings)
    {scope binder initializer}
    (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
      (source named) binder initializer) (childFuel : Nat) :
    ∀ candidate ∈ site.binding.atContext [], Nonempty (BindingProfile
      (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt)
      site.binding candidate) := by
  intro candidate member
  obtain ⟨profile⟩ := profiles site.binding (binding_member site.located) site.bindingCaller candidate member
  have original := profile.original
  rw [site.bindingInitializer] at original
  exact ⟨original⟩

/-- Body eligibility follows the same actual catalog row and original source. -/
theorem Rows.bodies_at_site {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (reasonAt : ExpressionId → Word)
    (profiles : Rows prepared named prepared.base.locals.bindings)
    {scope binder initializer}
    (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
      (source named) binder initializer) (childFuel : Nat) :
    ∀ candidate ∈ site.binding.atContext [], Nonempty (GeneralizedLocalBodyProfile.Profile
      (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).locals
      (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).current.owner
      candidate.source initializer) := by
  intro candidate member
  obtain ⟨profile⟩ := profiles site.binding (binding_member site.located) site.bindingCaller candidate member
  have body := profile.body
  rw [site.bindingInitializer] at body
  exact ⟨body⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedInitializerProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodySupport
/-! The selected named body obtains its bounded mixed-cell tree from its
original accepted compiler action. All row checks inspect the unchanged local
catalog; native child typing comes from the enclosing actual body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodySupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open CompatibleEncoding (bind_ok)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

def policy : SourceCoreLoops.Policy :=
  AcceptedNamedBodyFlow.namedPolicy prepared named diagnostics compiled.parents compiled.own

def scope (named : SourceCoreGeneralFunctions.Function) : SourceCoreLocalCell.Scope :=
  named.inputs.reverse.map fun binding => (binding.1.id, binding.2)

structure Profile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) : Type where
  initializers : CellAwareNamedInitializerProfiles.Rows prepared named prepared.base.locals.bindings
  scan : CellAwareSourceBodyAdmission.Scan prepared.base.locals named.signature.key [] (source named)
    approved expected true statements

def profile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    Option (Profile prepared named statements approved expected) := do
  let ⟨initializers⟩ ← CellAwareNamedInitializerProfiles.rows? prepared named prepared.base.locals.bindings
  let ⟨scan⟩ ← CellAwareSourceBodyAdmission.scan? prepared.base.locals named.signature.key []
    (source named) expression expected prepared.fuel true statements
  pure ⟨initializers, scan⟩

structure Body (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (sourceContext : SourceSemantics.Context) (expected : TypeSystem.Ty) where
  flow : Expr
  tree : CellAwareNativeBodyTree.Tree prepared named compiled certificates administrative
    (diagnostics.reasonAt named.signature.key) sourceContext (scope named) true compiled.statements
    expected named.signature.resultType flow
  emitted : compiled.body = CompatibleStatements.finish named.signature.resultType flow
    compiled.own.fellThroughReason compiled.own.table.escapedReason

/-- The public-facing static producer consumes checker facts and actual native
body typing; terminal certificates remain static compiler receipts. -/
theorem of_compilation
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {approved : ExpressionId → Prop} {expected : TypeSystem.Ty}
    (profile : Profile prepared named compiled.statements approved expected)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {administrative : Core.Context}
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      (policy compiled).lowerExpression fuel (source named) scope id (diagnostics.reasonAt named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) (scope named) sourceContext)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (Body compiled certificates administrative sourceContext expected) := by
  have accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy compiled) prepared.fuel (source named)
      (scope named) compiled.statements named.signature.resultType (diagnostics.reasonAt named.signature.key)
      compiled.own.fellThroughReason compiled.own.table.escapedReason = .ok compiled.body := compiled.bodyCompiled
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := bind_ok accepted
  have emitted : compiled.body = CompatibleStatements.finish named.signature.resultType flow
      compiled.own.fellThroughReason compiled.own.table.escapedReason := (Except.ok.inj emitted).symm
  rw [emitted] at nativeTyped
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  have tree := CellAwareNativeBodyCollectors.collected compiled record rfl rfl rfl
    (CellAwareNamedInitializerProfiles.Rows.at_site compiled _ profile.initializers)
    (CellAwareNamedInitializerProfiles.Rows.bodies_at_site compiled _ profile.initializers)
    children (profile.scan.syntax unique result typed) declarations generated flowTyped
  exact ⟨⟨flow, tree, emitted⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSyntax
/-! The bounded mixed-cell expression grammar keeps ordinary leaf policies
and generalized local reads distinct. Every accepted child belongs to the
original source graph; local-read normalization is retained at that leaf. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSyntax
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)

inductive Form : ExpressionForm → Prop where
  | literal {form} (atomic : CompatibleExpressionLiterals.Atomic form) : Form form
  | read (name : String) (binder : Resolved.LocalId) : Form (.reference name (.local binder))
  | builtin (name : String) (function : BuiltinFunctionId) : Form (.reference name (.builtinFunction function))
  | unary (operator : Syntax.UnaryOp) (operand : ExpressionId) : Form (.unary operator operand)
  | binary (operator : Syntax.BinaryOp) (left right : ExpressionId) : Form (.binary left operator right)
  | index (base key : ExpressionId) : Form (.index base key)
  | group (inner : ExpressionId) : Form (.group inner)
  | conditional (condition thenId elseId : ExpressionId) : Form (.conditional condition thenId elseId)
  | pair (left right : ExpressionId) : Form (.tuple [left, right])
  | call (callee : ExpressionId) (arguments : List ExpressionId) (metadata : IndirectCallResolution)
      (coercions : metadata.argumentCoercions = []) : Form (.call callee arguments (.indirect metadata))

structure Site {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : Form node.form
  coercions : node.coercions = []
  requirements : (match node.form with | .integerLiteral .. => True | _ => node.requirements = [])
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  ordinary : ∀ name binder, node.form = .reference name (.local binder) →
    prepared.base.locals.bindings.any (fun binding =>
      decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = false

private def form? (form : ExpressionForm) : Option (PLift (Form form)) :=
  match form with
  | .integerLiteral literal resolution => some ⟨.literal (.integer literal resolution)⟩
  | .reference name (.builtinBoolean value) => some ⟨.literal (.bool name value)⟩
  | .literal literal => some ⟨.literal (.word literal)⟩
  | .tuple [] => some ⟨.literal .unit⟩
  | .reference name (.local binder) => some ⟨.read name binder⟩
  | .reference name (.builtinFunction function) => some ⟨.builtin name function⟩
  | .conditional condition thenId elseId => some ⟨.conditional condition thenId elseId⟩
  | .unary operator operand => some ⟨.unary operator operand⟩
  | .binary left operator right => some ⟨.binary operator left right⟩
  | .index base key => some ⟨.index base key⟩
  | .group inner => some ⟨.group inner⟩
  | .tuple [left, right] => some ⟨.pair left right⟩
  | .call callee arguments (.indirect metadata) =>
    if empty : metadata.argumentCoercions = [] then some ⟨.call callee arguments metadata empty⟩ else none
  | _ => none

private def ordinary? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) :
    Option (PLift (∀ name binder, node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = false)) := by
  cases form : node.form
  case reference name resolution =>
    cases resolution
    case «local» binder =>
      exact if ordinary : prepared.base.locals.bindings.any (fun binding =>
          decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = false then
        some ⟨by
          intro actual actualBinder same
          obtain ⟨rfl, resolution⟩ := ExpressionForm.reference.inj same
          cases resolution
          exact ordinary⟩
      else none
    all_goals exact some ⟨by intro name binder same; simp at same⟩
  all_goals exact some ⟨by intro name binder same; simp at same⟩

private def requirements? (node : ExpressionNode) :
    Option (PLift (match node.form with | .integerLiteral .. => True | _ => node.requirements = [])) :=
  if empty : node.requirements = [] then
    some ⟨by split <;> simp_all⟩
  else
    match form : node.form with
    | .integerLiteral .. => some ⟨True.intro⟩
    | _ => none

def site? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (Site prepared named source id) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node => do
    let ⟨form⟩ ← form? node.form
    if coercions : node.coercions = [] then do
      let ⟨requirements⟩ ← requirements? node
      if notInitializer : prepared.base.locals.bindings.find? (fun binding =>
          decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none then do
        let ⟨ordinary⟩ ← ordinary? prepared named node
        pure ⟨node, found, form, coercions, requirements, notInitializer, ordinary⟩
      else none
    else none

inductive Syntax {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) : ExpressionId → Prop where
  | literal {id} (site : Site prepared named source id)
      (atomic : CompatibleExpressionLiterals.Atomic site.node.form) : Syntax prepared named source id
  | read {id name binder} (site : Site prepared named source id)
      (form : site.node.form = .reference name (.local binder)) : Syntax prepared named source id
  | builtin {id name function} (site : Site prepared named source id)
      (form : site.node.form = .reference name (.builtinFunction function)) : Syntax prepared named source id
  | generalized {id} (observed : GeneralizedLocalNamedReadCompilation.Observations prepared named source id)
      (recipe : GeneralizedLocalNamedRecipeCompilation.Observations prepared named source id) :
      Syntax prepared named source id
  | unary {id operator operand} (site : Site prepared named source id)
      (form : site.node.form = .unary operator operand)
      (child : Syntax prepared named source operand) : Syntax prepared named source id
  | binary {id operator left right} (site : Site prepared named source id)
      (form : site.node.form = .binary left operator right)
      (first : Syntax prepared named source left) (second : Syntax prepared named source right) :
      Syntax prepared named source id
  | index {id base key} (site : Site prepared named source id)
      (form : site.node.form = .index base key)
      (first : Syntax prepared named source base) (second : Syntax prepared named source key) :
      Syntax prepared named source id
  | group {id inner} (site : Site prepared named source id) (form : site.node.form = .group inner)
      (child : Syntax prepared named source inner) : Syntax prepared named source id
  | conditional {id condition thenId elseId} (site : Site prepared named source id)
      (form : site.node.form = .conditional condition thenId elseId)
      (test : Syntax prepared named source condition) (yes : Syntax prepared named source thenId)
      (no : Syntax prepared named source elseId) : Syntax prepared named source id
  | pair {id left right} (site : Site prepared named source id) (form : site.node.form = .tuple [left, right])
      (first : Syntax prepared named source left) (second : Syntax prepared named source right) :
      Syntax prepared named source id
  | call {id callee arguments metadata} (site : Site prepared named source id)
      (form : site.node.form = .call callee arguments (.indirect metadata))
      (calleeObserved : GeneralizedLocalNamedReadCompilation.Observations prepared named source callee)
      (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Observations prepared named source callee)
      (children : ∀ child ∈ arguments, Syntax prepared named source child) : Syntax prepared named source id

private def all? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← all? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

def syntax? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Syntax prepared named source id))
  | 0, _ => none
  | fuel + 1, id =>
    match GeneralizedLocalNamedReadCompilation.observations? prepared named source id with
    | some observed => do
      let recipe ← GeneralizedLocalNamedRecipeCompilation.observations? prepared named source id
      pure ⟨.generalized observed recipe⟩
    | none => do
      let site ← site? prepared named source id
      match form : site.node.form with
      | .integerLiteral literal resolution => pure ⟨.literal site (form ▸ .integer literal resolution)⟩
      | .reference name (.builtinBoolean value) => pure ⟨.literal site (form ▸ .bool name value)⟩
      | .literal literal => pure ⟨.literal site (form ▸ .word literal)⟩
      | .tuple [] => pure ⟨.literal site (form ▸ .unit)⟩
      | .reference _name (.local _binder) => pure ⟨.read site form⟩
      | .reference _name (.builtinFunction _function) => pure ⟨.builtin site form⟩
      | .conditional condition thenId elseId => do
        let ⟨test⟩ ← syntax? prepared named source fuel condition
        let ⟨yes⟩ ← syntax? prepared named source fuel thenId
        let ⟨no⟩ ← syntax? prepared named source fuel elseId
        pure ⟨.conditional site form test yes no⟩
      | .unary _operator operand => do
        let ⟨child⟩ ← syntax? prepared named source fuel operand
        pure ⟨.unary site form child⟩
      | .binary left _operator right => do
        let ⟨first⟩ ← syntax? prepared named source fuel left
        let ⟨second⟩ ← syntax? prepared named source fuel right
        pure ⟨.binary site form first second⟩
      | .index base key => do
        let ⟨first⟩ ← syntax? prepared named source fuel base
        let ⟨second⟩ ← syntax? prepared named source fuel key
        pure ⟨.index site form first second⟩
      | .group inner => do
        let ⟨child⟩ ← syntax? prepared named source fuel inner
        pure ⟨.group site form child⟩
      | .tuple [left, right] => do
        let ⟨first⟩ ← syntax? prepared named source fuel left
        let ⟨second⟩ ← syntax? prepared named source fuel right
        pure ⟨.pair site form first second⟩
      | .call callee arguments (.indirect _metadata) => do
        let calleeObserved ← GeneralizedLocalNamedReadCompilation.observations? prepared named source callee
        let calleeRecipe ← GeneralizedLocalNamedRecipeCompilation.observations? prepared named source callee
        let ⟨children⟩ ← all? (Syntax prepared named source) (syntax? prepared named source fuel) arguments
        pure ⟨.call site form calleeObserved calleeRecipe children⟩
      | _ => none

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSyntax
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
/-! Ordinary sites derive their actual named compiler policy from finite raw
metadata observations. The generalized read branch retains its distinct
successful override and is never assigned an ordinary bypass law. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site Form)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}

theorem contextual (site : Site prepared named source id) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic =>
    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]
  | read name binder =>
    have ordinary := site.ordinary name binder shape
    simp only [SourceCoreGeneralFunctions.contextualSource, site.found, bind, Except.bind, pure, Except.pure, shape, ordinary, Bool.false_eq_true, ↓reduceIte]
  | index base key | unary operator operand | binary operator left right | conditional condition thenId elseId | builtin name function | group inner | pair left right | call callee arguments metadata coercions =>
    simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]

private theorem evidence_none (site : Site prepared named source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? site.node = some site.node.requirements := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [site.coercions]
    change (if site.node.requirements.length < 0 then none else
      if site.node.requirements = site.node.requirements.take (site.node.requirements.length - 0) ++ [] then
        some (site.node.requirements.take (site.node.requirements.length - 0)) else none) = some site.node.requirements
    simp
  have supported := site.form
  have requirements := site.requirements
  generalize shape : site.node.form = form at supported requirements
  cases supported with
  | literal atomic =>
    cases atomic with
    | integer literal resolution =>
      simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, site.coercions]
    | unit | bool name value | word literal =>
      simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
  | index base key | unary operator operand | binary operator left right | conditional condition thenId elseId | builtin name function | read name binder | group inner | pair left right =>
    simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
  | call callee arguments metadata coercions =>
    simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions, coercions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- Only a real ordinary site has an empty special result. -/
theorem special (site : Site prepared named source id) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic => cases atomic <;> simp
  | read name binder =>
    simp only
    rw [site.ordinary name binder shape]
    rfl
  | index base key | unary operator operand | binary operator left right | conditional condition thenId elseId | builtin name function | group inner | pair left right | call callee arguments metadata coercions => simp

theorem read (site : Site prepared named source id) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates
/-! The mixed-cell compiler tree retains ordinary literal/read receipts,
actual generalized read wrappers, and the exact ordered indirect children.
No called-body execution or dynamic result appears in a constructor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (rootFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | plain {id lowered}
      (receipt : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate prepared.fuel
        (.initial checked) source sourceContext (context prepared named).solvedRequirements reasonAt scope id lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | builtin {id lowered}
      (receipt : CellAwareBuiltinValueCertificates.Header prepared source id lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | generalized {id lowered}
      (receipt : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered)
      (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt receipt) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode) (type : node.type = innerNode.type)
      (child : Tree compiled rootFuel source sourceContext reasonAt scope inner lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (type : node.type = .product leftNode.type rightNode.type)
      (leftChild : Tree compiled rootFuel source sourceContext reasonAt scope left first)
      (rightChild : Tree compiled rootFuel source sourceContext reasonAt scope right second) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header (.initial checked) source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (firstChild : Tree compiled rootFuel source sourceContext reasonAt scope base first)
      (secondChild : Tree compiled rootFuel source sourceContext reasonAt scope key second) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
          first.expression second.expression (reasonAt id)⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core)
      (child : Tree compiled rootFuel source sourceContext reasonAt scope operand ⟨core.operandType, childCode⟩) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode)
      (first : Tree compiled rootFuel source sourceContext reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Tree compiled rootFuel source sourceContext reasonAt scope right ⟨mode.operandType operator, rightCode⟩) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩

  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : Tree compiled rootFuel source sourceContext reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree compiled rootFuel source sourceContext reasonAt scope thenId ⟨type, thenCode⟩)
      (elseTree : Tree compiled rootFuel source sourceContext reasonAt scope elseId ⟨type, elseCode⟩) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩
  | call {id callee ids metadata fuel lowered types}
      (compiler : CallableIndirectCallCertificates.Receipt (namedPolicy compiled rootFuel) (namedLowerBody compiled)
        fuel (context prepared named) source scope id callee ids metadata reasonAt lowered)
      (calleeReceipt : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope callee reasonAt compiler.calleeCode)
      (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeReceipt)
      (parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes)
      (children : ∀ child lowered, (child, lowered) ∈ compiler.entries →
        Tree compiled rootFuel source sourceContext reasonAt scope child lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionScalarProjection
/-! Scalar operand selection follows the actual emitted type. Generalized
read bundles and builtin handles have a product carrier and cannot pass the
compiler's scalar operand check. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionScalarProjection
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy)
open CellAwareNamedExpressionCertificates (Tree)

def Scalar (type : Core.Ty) : Prop := type = .bool ∨ type = .word ∨ type = .integer

private theorem function_not_scalar (parameter result : Core.Ty) :
    ¬ Scalar (CallableContract.functionType parameter result) := by
  simp [Scalar, CallableContract.functionType]

theorem unary_input_scalar (operator : Syntax.UnaryOp) (type : Core.Ty) :
    Scalar (CompatibleExpressionConditionals.selectedUnary operator type).operandType := by
  unfold CompatibleExpressionConditionals.selectedUnary
  split
  · simp [Scalar, UnaryOp.operandType]
  · cases operator <;> simp [Scalar, SourceCorePrimitive.unaryOperator, UnaryOp.operandType]

theorem binary_input_scalar (mode : CompatibleExpressionPrimitives.Mode) (operator : Syntax.BinaryOp) :
    Scalar (mode.operandType operator) := by
  cases mode <;> cases operator <;>
    simp [Scalar, CompatibleExpressionPrimitives.Mode.operandType,
      SourceCorePrimitive.binaryOperandType, SourceCoreInteger.binaryOperandType]

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compiled : Compilation prepared named diagnostics code} {rootFuel : Nat}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

theorem projected (tree : Tree compiled rootFuel source sourceContext reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (scalar : Scalar lowered.type) : checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | plain receipt => exact CompatibleExpressionPrimitives.Tree.projected (.product receipt.1) found
  | builtin receipt =>
    exact False.elim (function_not_scalar _ _ (receipt.nativeType ▸ scalar))
  | generalized receipt recipe =>
    exact False.elim (function_not_scalar _ _ (recipe.nativeType ▸ (receipt.type.symm ▸ scalar)))
  | group metadata _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | pair metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | index header _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans header.metadata.found)
    exact header.metadata.projected
  | unary metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | binary metadata _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | call compiler _ _ _ _ _ =>
    have contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
      simp [SourceCoreGeneralFunctions.contextualSource, compiler.found, compiler.originalForm]
    have read := compiler.read
    simp only [namedPolicy, contextual, bind, Except.bind] at read
    change SourceCoreCompatibleDataExpressions.readExpression checked source id = .ok (compiler.node, compiler.type) at read
    have metadata := CompatibleExpressionReads.metadata_of_read read
    cases Option.some.inj (found.symm.trans metadata.found)
    have nativeType : lowered.type = compiler.type := congrArg (fun output => output.type) compiler.output
    exact metadata.projected.trans (congrArg Except.ok nativeType.symm)

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionScalarProjection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCollectors
/-! Accepted named expression compilation yields the mixed tree recursively.
Original Source typing selects each physical child; no child execution is an
input to this extraction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareNamedExpressionCertificates (Tree)
open CompatibleEncoding (bind_ok)

section Generic
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

private theorem call_read {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {resolution : IndirectCallResolution}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect resolution))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation
      source scope id reasonAt = .ok lowered) :
    ∃ type, policy.readExpression source id = .ok (node, type) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation
        childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form, readPolicy] at accepted
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        exact ⟨type, readPolicy.trans read⟩
  · simp [owner, bind, Except.bind] at accepted

private theorem child_certificates {scope : SourceCoreLocalCell.Scope} {budget : Nat}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget
      compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code →
      certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      ∀ id code, (id, code) ∈ ids.zip codes → certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_⟩
      intro other otherCode member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact child
      · exact children other otherCode remaining

end Generic

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code) (rootFuel : Nat)
  {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}

private theorem special {id : ExpressionId} (site : Site prepared named source id) :
    ∀ child budget, (match (namedPolicy compiled rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareNamedExpressionPolicies.special compiled site rootFuel child budget scope reasonAt

private theorem plain {id : ExpressionId} (site : Site prepared named source id)
    (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    (empty : site.node.form.references = [])
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id site.node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Tree compiled rootFuel source sourceContext reasonAt scope id lowered := by
  have policy : CompatibleExpressionProducts.PolicyOn (namedPolicy compiled rootFuel) (context prepared named)
      prepared.fuel (.initial checked) source scope reasonAt (fun child => child = id) := {
    special := by intro child same _; subst child; exact special compiled rootFuel site
    read := by intro child same _; subst child; exact CellAwareNamedExpressionPolicies.read compiled site rootFuel
    lower := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe compiled rootFuel).lowerRead
    leaf := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe compiled rootFuel).leafLowerer }
  apply Tree.plain
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations policy
    ?_ ?_ syntaxTree rfl site.found typed accepted
  · intro parent node child same found member
    subst parent
    have sameNode := Option.some.inj (site.found.symm.trans found)
    subst node
    rw [empty] at member
    cases member
  · intro child node same _ found
    subst child
    have sameNode := Option.some.inj (site.found.symm.trans found)
    exact sameNode ▸ site.coercions

private theorem builtin {id : ExpressionId} (site : Site prepared named source id)
    {name : String} {function : BuiltinFunctionId}
    (form : site.node.form = .reference name (.builtinFunction function))
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Nonempty (CellAwareBuiltinValueCertificates.Header prepared source id lowered) := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, site.found,
        bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special compiled rootFuel (scope := scope) (reasonAt := reasonAt) site
        (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
            (namedLowerBody compiled) (min budget fuel) (context prepared named)
            childSource childScope childId childReasonAt) (fuel + 1)
      change CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
        (context prepared named) _ _ _ _ _ _ = .ok none at bypass
      simp only [show (namedPolicy compiled rootFuel).lowerSpecial? = some
        (CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel) from rfl] at accepted
      rw [bypass] at accepted
      simp only [form,
        CellAwareNamedExpressionPolicies.read compiled site rootFuel] at accepted
      obtain ⟨pair, read, rest⟩ := bind_ok accepted
      obtain ⟨other, type⟩ := pair
      have metadata := CompatibleExpressionReads.metadata_of_read read
      have same := Option.some.inj (metadata.found.symm.trans site.found)
      subst other
      simp only [form] at rest
      obtain ⟨code, reference, rest⟩ := bind_ok rest
      obtain ⟨done, _sameType, rest⟩ := bind_ok rest
      cases done
      cases rest
      exact CellAwareBuiltinValueCertificates.of_reference prepared rfl site.found form
        metadata.requirements metadata.coercions reference
    · simp [owner, bind, Except.bind] at accepted

/-- The actual root callback remains fixed while each recursive child uses
its true smaller compiler budget. -/
theorem of_policy {id : ExpressionId}
    (syntaxTree : CellAwareNamedExpressionSyntax.Syntax prepared named source id)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Tree compiled rootFuel source sourceContext reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | literal site atomic =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain compiled rootFuel site (.literal site.found atomic)
      (by generalize form : site.node.form = actual at atomic ⊢; cases atomic <;> rfl) unique declarations typed accepted
  | read site form =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain compiled rootFuel site (.read site.found form)
      (by simp [form, ExpressionForm.references]) unique declarations typed accepted
  | builtin site form =>
    obtain ⟨receipt⟩ := builtin compiled rootFuel site form accepted
    exact .builtin receipt
  | generalized observed recipe =>
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := GeneralizedLocalNamedReadCompilation.of_policy compiled observed accepted
      obtain ⟨recipe⟩ := GeneralizedLocalNamedRecipeCompilation.of_certificate recipe receipt
      exact .generalized receipt recipe
  | index site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types
        unique site.found form site.coercions typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨keyNode, keyContains, actualKeyType⟩ := keyTyped.stored_type
      have baseFound := lookupExpression?_complete unique baseContains
      have keyFound := lookupExpression?_complete unique keyContains
      rw [← actualKeyType] at keyTyped baseType baseTyped
      rw [← baseType] at baseTyped
      obtain ⟨layout, comparison, firstCode, secondCode, rfl, header, firstGenerated, secondGenerated⟩ :=
        CompatibleExpressionIndices.index_of_functions
          (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
          (context := context prepared named) (values := .initial checked)
          (scope := scope) (reasonAt := reasonAt) site.found baseFound form
          (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel)
          (by rfl) accepted
      exact .index header keyFound form baseType (firstIH baseFound baseTyped firstGenerated)
        (secondIH keyFound keyTyped secondGenerated)
  | unary site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | @unary operator operand childCode otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          CompatibleExpressionPrimitives.unary_source_types unique site.found form metadata.coercions metadata.requirements typed
        have childTree := ih childFound childTyped generated
        have scalar : CellAwareNamedExpressionScalarProjection.Scalar childCode.type :=
          inputChecked ▸ CellAwareNamedExpressionScalarProjection.unary_input_scalar _ childCode.type
        have chosen := CompatibleExpressionConditionals.unary_selected profile
          (CellAwareNamedExpressionScalarProjection.projected childTree childFound scalar)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, native⟩ := childCode
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact .unary metadata form childFound rfl rfl profile childTree
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | binary site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, sameType, leftTyped, rightTyped, profile⟩ :=
          CompatibleExpressionPrimitives.binary_source_types unique site.found form metadata.coercions metadata.requirements typed
        have firstTree := firstIH leftFound leftTyped firstGenerated
        have secondTree := secondIH rightFound rightTyped secondGenerated
        have scalar : CellAwareNamedExpressionScalarProjection.Scalar first.type :=
          leftChecked ▸ CellAwareNamedExpressionScalarProjection.binary_input_scalar
            (CompatibleExpressionConditionals.selectedMode first.type) _
        have chosen := CompatibleExpressionConditionals.binary_selected profile
          (CellAwareNamedExpressionScalarProjection.projected firstTree leftFound scalar)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact .binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | conditional site form test yes no testIH thenIH elseIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | conditional otherForm metadata testGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨testNode, thenNode, elseNode, testFound, thenFound, elseFound,
            testType, thenType, elseType, testTyped, thenTyped, elseTyped⟩ :=
          CompatibleExpressionConditionals.conditional_source_types unique site.found form site.coercions typed
        exact .conditional metadata form testFound thenFound elseFound testType thenType elseType
          (testIH testFound testTyped testGenerated) (thenIH thenFound thenTyped thenGenerated)
          (elseIH elseFound elseTyped elseGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ =>
        simp [form] at otherForm
  | group site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | group otherForm metadata generated =>
        cases ExpressionForm.group.inj (form.symm.trans otherForm)
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types unique site.found form site.coercions typed
        exact .group metadata form innerFound sourceType (ih innerFound childTyped generated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | pair site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | pair otherForm metadata firstGenerated secondGenerated =>
        obtain ⟨rfl, rfl⟩ := by simpa using ExpressionForm.tuple.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          CompatibleExpressionProducts.pair_source_types unique site.found form site.coercions typed
        exact .pair metadata form leftFound rightFound sourceType
          (firstIH leftFound leftTyped firstGenerated) (secondIH rightFound rightTyped secondGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | @call id callee ids metadata site form calleeObserved calleeRecipe children ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have bypass := special compiled rootFuel (scope := scope) (reasonAt := reasonAt) site
      have readPolicy := CellAwareNamedExpressionPolicies.read compiled site rootFuel
      obtain ⟨type, read⟩ := call_read (values := .initial checked) site.found form bypass readPolicy accepted
      obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (compilation := context prepared named) (scope := scope) (reasonAt := reasonAt)
        site.found form bypass read form accepted
      have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler readPolicy
      have originalSame := Option.some.inj (compiler.found.symm.trans site.found)
      have parentTyped : ExpressionHasType source sourceContext id compiler.original.type := by
        simpa [originalSame] using typed
      obtain ⟨parameter, result, types, _calleeTyped, argumentsTyped, _bundle, _result⟩ :=
        CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
          compiler parent unique parentTyped
      obtain ⟨calleeReceipt⟩ : Nonempty (GeneralizedLocalNamedReadCompilation.Certificate
          prepared named source scope callee reasonAt compiler.calleeCode) := by
        cases fuel with
        | zero =>
          have impossible := compiler.calleeAccepted
          simp [SourceCoreFunctions.lowerExpressionWithPolicy] at impossible
        | succ fuel =>
          exact GeneralizedLocalNamedReadCompilation.of_policy compiled calleeObserved compiler.calleeAccepted
      obtain ⟨calleeRecipe⟩ := GeneralizedLocalNamedRecipeCompilation.of_certificate calleeRecipe calleeReceipt
      have calleeCertified : Tree compiled rootFuel source sourceContext reasonAt scope callee compiler.calleeCode :=
        .generalized calleeReceipt calleeRecipe
      obtain ⟨count, nodes, certified⟩ := child_certificates unique argumentsTyped compiler.argumentsAccepted
        (fun child member childNode lowered childFound childTyped childAccepted =>
          ih child member childFound childTyped childAccepted)
      refine .call compiler calleeReceipt calleeRecipe parent (CompatibleExpressionConstructors.sequence_of_nodes count nodes ?_) ?_
      · intro child lowered member
        exact ⟨rfl, List.mem_cons_of_mem _ member⟩
      · intro child lowered member
        rcases List.mem_cons.mp member with head | remaining
        · cases head; exact calleeCertified
        · exact certified child lowered remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyProducer
/-! The bounded named profile fills every terminal compiler receipt from its
actual accepted expression action. Its public construction has no expression
certificate callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyProducer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

abbrev Profile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :=
  CellAwareNamedBodySupport.Profile prepared named statements
    (CellAwareNamedExpressionSyntax.Syntax prepared named (source named)) expected

def profile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :
    Option (Profile prepared named statements expected) :=
  CellAwareNamedBodySupport.profile? prepared named statements
    (CellAwareNamedExpressionSyntax.syntax? prepared named (source named) prepared.fuel) expected

def Certificate (compiled : Compilation prepared named diagnostics code)
    (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ rootFuel,
    CellAwareNamedExpressionCertificates.Tree compiled rootFuel (source named) sourceContext
      (diagnostics.reasonAt named.signature.key) scope id lowered

theorem expression (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (syntaxTree : CellAwareNamedExpressionSyntax.Syntax prepared named (source named) id)
    (unique : NodeOccurrencesUnique (source named))
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    (found : (source named).lookupExpression? id = some node)
    (typed : ExpressionHasType (source named) sourceContext id node.type)
    (accepted : (CellAwareNamedBodySupport.policy compiled).lowerExpression fuel (source named)
      scope id (diagnostics.reasonAt named.signature.key) = .ok lowered) :
    Certificate compiled sourceContext scope id lowered := by
  change SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
    prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
    diagnostics (context prepared named) prepared.base.callableContext none none fuel
    (source named) scope id (diagnostics.reasonAt named.signature.key) = .ok lowered at accepted
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual compiled record] at accepted
    exact ⟨fuel, CellAwareNamedExpressionCollectors.of_policy compiled fuel syntaxTree unique
      declarations found typed accepted⟩

theorem of_compilation (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {expected : TypeSystem.Ty} (profile : Profile prepared named compiled.statements expected)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named)
      (CellAwareNamedBodySupport.scope named) sourceContext)
    {administrative : Core.Context} {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (CellAwareNamedBodySupport.scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (CellAwareNamedBodySupport.Body compiled (Certificate compiled) administrative sourceContext expected) := by
  apply CellAwareNamedBodySupport.of_compilation compiled record profile ?_ unique result typed declarations nativeTyped
  intro childContext childScope fuel id node lowered childDeclarations syntaxTree found childTyped accepted _ _
  exact expression compiled record syntaxTree unique childDeclarations found childTyped accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedIndexDiagnostics
/-! Actual named compilation supplies each index occurrence's original issuer.
The current public receiver supplies its missing-default diagnostic only when
that lookup is reached. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedIndexDiagnostics
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority

def Ready (compiled : SourceCoreUnifiedCompilation.Compiled) (source : TypedSource)
    (reasonAt : ExpressionId → Word) : Prop :=
  ∀ {id base node baseNode layout comparison first second}
    (header : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second),
    Nonempty (Port compiled header (reasonAt id))

theorem ready {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {reasonAt : ExpressionId → Word}
    (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named reasonAt)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {source : TypedSource} (sourceEq : source = CallableIndexedNamedGeneration.source named)
    (unique : NodeOccurrencesUnique source) : Ready compiled source reasonAt := by
  intro id base node baseNode layout comparison first second header
  obtain ⟨issued,present,callback,_own,_ownFound⟩ := issuer
  exact ⟨{
    owner := named.signature.key
    row := named.specialized
    record := record
    sourceEq := sourceEq
    unique := unique
    issuer := issued
    present := present
    token := congrFun callback id }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedIndexDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics
/-! Every ordinary read in the mixed named body uses its original issued
occurrence and token at the current public receiver. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {reasonAt : ExpressionId → Word}
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named reasonAt)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  {invocation : Staging.Recursive.Scope}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)

include issuer record receiver sourceEq unique in
/-- The actual read certificate fixes the binder; the selected compiler row
and retained issuer fix the diagnostic, including its original source span. -/
theorem uninitialized {fuel : Nat} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered) (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  obtain ⟨issued, present, callback, own, ownFound⟩ := issuer
  have originalSource : invocation.source = named.specialized.function.typedBody := sourceEq
  have contains : ContainsExpression named.specialized.function.typedBody id certificate.node :=
    by simpa only [originalSource] using lookupExpression?_sound certificate.metadata.found
  have originalUnique : NodeOccurrencesUnique named.specialized.function.typedBody := by simpa only [originalSource] using unique
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      record originalUnique contains certificate.form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  exact CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [callback, token] using decoded) (.readUninitialized location certificate.binder)

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyReceipt
/-! The actual public preparation and named header produce the bounded mixed
body certificate. Source typing, parameter declarations and native body typing
are recovered from their original receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
theorem of_header_selected
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies whole)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareNamedBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareNamedBodySupport.Body prepared.compilation
      (CellAwareNamedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) := by
  have sourceEq : header.function.source = source prepared.named := by
    rw [header.agreement.source, aligned.named]
    rfl
  have statementsEq : header.function.body = prepared.compilation.statements := by
    rw [aligned.function]
    rfl
  have resultEq : header.function.resultType = prepared.named.specialized.function.inferredBodyType := by
    rw [header.agreement.result, aligned.named]
  have record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan
      prepared.named.signature.key = .ok prepared.named.specialized := by
    simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record whole header
  have native := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed)
    (values := SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
    (prepared := whole.indexed.ancestry) (program := Program.ofChecked whole.sourceProgram) header
  obtain ⟨final, facts, typed, _⟩ := (SelectedCompilationHeaderCertificates.certified bodyTyping header).statements
  rw [sourceEq, statementsEq] at typed
  apply CellAwareNamedBodyProducer.of_compilation prepared.compilation record
    (by simpa only [resultEq] using profile) (sourceEq ▸ header.unique) rfl typed
  · simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope, aligned.bindings,
      CellAwareNamedBodySupport.scope] using declarations
  · simpa only [CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.parameterScope,
      aligned.bindings, aligned.body, CellAwareNamedBodySupport.scope] using native

/- Compatibility adapters for callers with a whole-program receipt. -/
include aligned in
theorem of_header
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareNamedBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareNamedBodySupport.Body prepared.compilation
      (CellAwareNamedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) := by
  apply of_header_selected (bodyTyping := SelectedCompilationBodyTyping.Bodies.of_program wellFormed) (aligned := aligned) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap
/-! Actual parameter allocation and the reached staged fault determine deep
heap typing. Both semantic faults and earlier stage stops use the same original
Source body certificate; native result shapes supply no typing premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedAdmittedBodyEntries

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (support : SelectedCompilationNamedSupport.Support compiled)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {scope : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages compiled).Closure header.function scope)
  {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
  (heapTyped : Dynamic.HeapWellTyped header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)

include support selected heapTyped argumentsTyped allocated in
theorem after_fault_selected {size : Nat} {finalContext : SourceSemantics.Context} {failure : Staging.Recursive.Failure}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) size scope header.context environment bound
      header.function.body finalContext (.fault failure) after) :
    Dynamic.HeapWellTyped header.context after := by
  have receipt := SelectedCompilationNamedAdmission.parameter_source (support.certified header) allocated heapTyped argumentsTyped
  have sourceEq := (SelectedCompilationPhysicalProgramSupport.stages compiled).source selected
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context scope.source := by
    simpa only [sourceEq] using receipt.runtime
  have covers : scope.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages compiled).evidence selected] using receipt.covers
  obtain ⟨final, facts, typed, _complete⟩ := receipt.bodyTyped
  have actualTyped : StatementsHaveType scope.source { returnType := header.function.resultType }
      header.context header.function.body final facts := by
    simpa only [sourceEq] using typed
  exact (Staging.Recursive.SelectedPreservation.statements support.registryBodies
    runtime covers receipt.locals receipt.heapTyped actualTyped trace).heap_typed

/- Compatibility adapters for callers with a whole-program receipt. -/
include wellFormed selected heapTyped argumentsTyped allocated in
theorem after_fault {size : Nat} {finalContext : SourceSemantics.Context} {failure : Staging.Recursive.Failure}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) size scope header.context environment bound
      header.function.body finalContext (.fault failure) after) :
    Dynamic.HeapWellTyped header.context after := by
  apply after_fault_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (selected := selected) (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (allocated := allocated) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedFaultHeap
end
