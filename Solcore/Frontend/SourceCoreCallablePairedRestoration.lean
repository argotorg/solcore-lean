import Solcore.Frontend.SourceCoreCallablePairedReadViews
import Solcore.Frontend.SourceCoreCallablePairedHeaders

/-! Source closure restoration from the actual paired callable profile.
Code authenticity and physical capture joins are supplied by the owning native
receipts. Prepared positions select raw lexical headers and exact read recipes;
restoration performs no source traversal, substitution or evidence resolution.

The output retains the original closure for an instantiated read. Produced and
stored wrappers keep the corresponding completion provenance. These receipts
establish the reconstruction boundary; full source execution meaning still
requires the enclosing native emission/history theorem.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedRestoration
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallablePairedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Headers := @SourceCoreCallablePairedHeaders.Prepared
abbrev Templates := @SourceCoreCallablePairedTemplates.Cache
abbrev Views := @SourceCoreCallablePairedReadViews.Cache
abbrev Ledger := @SourceCoreAllocationLedger.TypedLedger
abbrev SourceValue := SourceTypedRuntime.Value

inductive Error where
  | captures (error : SourceCoreCallablePairedCaptures.Error)
  | lexicalUnavailable
  | callerUnavailable
  | lambdaHeaderUnavailable (position : Nat) (descriptor : Core.Word)
  | principalHeaderUnavailable (position : Nat) (binder : Resolved.LocalId)
  | readRecipeUnavailable (caller lexical : Nat) (view target : Core.Word)
  deriving Repr

structure Ordinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallablePairedCaptures.Captured authenticated ledger
  position : Nat
  lookup : graph.table.lookupIndex? authenticated.snapshot.frame = some (some position)
  header : SourceCoreCallablePairedHeaders.LambdaHeader graph headers.principals
  selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor = some header
  source : SourceValue
  exact : source = header.sourceValue captures.environment

def restoreOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Ordinary headers authenticated ledger) := do
  let captures ← (SourceCoreCallablePairedCaptures.joinAuthenticated authenticated ledger).mapError Error.captures
  match lookup : graph.table.lookupIndex? authenticated.snapshot.frame with
  | some (some position) =>
    match selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor with
    | none => throw (.lambdaHeaderUnavailable position authenticated.template.source.lambda.descriptor)
    | some header => pure ⟨captures, position, lookup, header, selected, header.sourceValue captures.environment, rfl⟩
  | _ => throw .lexicalUnavailable

structure Read {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallablePairedCaptures.Captured authenticated.underlying ledger
  caller : Nat
  callerLookup : graph.table.lookupIndex? authenticated.caller.frame = some (some caller)
  lexical : Nat
  lexicalLookup : graph.table.lookupIndex? authenticated.underlying.snapshot.frame = some (some lexical)
  recipe : SourceCoreCallableAncestryPairedPreparation.Recipe graph.inputs graph.table
  recipeSelected : graph.recipeAt? caller lexical authenticated.wrapper.entry.id authenticated.wrapper.target = some recipe
  header : SourceCoreCallablePairedHeaders.PrincipalHeader graph headers.principals
  headerSelected : headers.principalBinderAt? lexical authenticated.wrapper.entry.view.binding.binder.id
    authenticated.wrapper.entry.view.principal.initializer = some header
  source : SourceValue
  exact : source = recipe.applied.sourceValue captures.environment header.principal.context.evidence

def restoreRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Read headers authenticated ledger) := do
  let captures ← (SourceCoreCallablePairedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  match callerLookup : graph.table.lookupIndex? authenticated.caller.frame with
  | some (some caller) =>
    match lexicalLookup : graph.table.lookupIndex? authenticated.underlying.snapshot.frame with
    | some (some lexical) =>
      match recipeSelected : graph.recipeAt? caller lexical authenticated.wrapper.entry.id authenticated.wrapper.target with
      | none => throw (.readRecipeUnavailable caller lexical authenticated.wrapper.entry.id authenticated.wrapper.target)
      | some recipe =>
        match headerSelected : headers.principalBinderAt? lexical authenticated.wrapper.entry.view.binding.binder.id
            authenticated.wrapper.entry.view.principal.initializer with
        | none => throw (.principalHeaderUnavailable lexical authenticated.wrapper.entry.view.binding.binder.id)
        | some header => pure ⟨captures, caller, callerLookup, lexical, lexicalLookup, recipe, recipeSelected,
            header, headerSelected, recipe.applied.sourceValue captures.environment header.principal.context.evidence, rfl⟩
    | _ => throw .lexicalUnavailable
  | _ => throw .callerUnavailable

/-- Native result provenance is retained alongside the source reconstruction. -/
structure ProducedOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (produced : SourceCoreCallablePairedCaptures.Produced templates completion world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  restored : Ordinary headers produced.authenticated ledger

def restoreProducedOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (produced : SourceCoreCallablePairedCaptures.Produced templates completion world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (ProducedOrdinary headers produced ledger) := do
  pure ⟨← restoreOrdinary headers produced.authenticated ledger⟩

structure ProducedRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    (produced : SourceCoreCallablePairedReadViews.Produced authenticated completion)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  restored : Read headers authenticated ledger

def restoreProducedRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    (produced : SourceCoreCallablePairedReadViews.Produced authenticated completion)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (ProducedRead headers produced ledger) := do
  pure ⟨← restoreRead headers authenticated ledger⟩

/-- Failed and suspended native heaps retain stored-payload provenance. -/
structure StoredOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedCaptures.Stored templates completion value ledger) where private mk ::
  restored : Ordinary headers stored.authenticated ledger

def restoreStoredOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedCaptures.Stored templates completion value ledger) :
    Except Error (StoredOrdinary headers stored) := do
  pure ⟨← restoreOrdinary headers stored.authenticated ledger⟩

structure StoredRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedReadViews.Stored authenticated completion ledger) where private mk ::
  restored : Read headers authenticated ledger

def restoreStoredRead {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
    {completion : SourceCoreCallablePairedPrograms.Completion program}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (stored : SourceCoreCallablePairedReadViews.Stored authenticated completion ledger) :
    Except Error (StoredRead headers stored) := do
  pure ⟨← restoreRead headers authenticated ledger⟩

namespace Ordinary
variable {checked : Checked} {program : Program checked} {graph : Graph program.base}
  {headers : Headers graph} {templates : Templates program}
  {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
  {authenticated : SourceCoreCallablePairedTemplates.Authenticated templates world store value}
  {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}

theorem raw_closure (restored : Ordinary headers authenticated ledger) :
    restored.source = .closure restored.header.parameters restored.header.resultType restored.header.body
      restored.header.state.metadata.source restored.header.state.metadata.owner restored.captures.environment
      restored.header.context.context.evidence := restored.exact

theorem capture_order (restored : Ordinary headers authenticated ledger) :
    restored.captures.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst := restored.captures.binders

end Ordinary
namespace Read
variable {checked : Checked} {program : Program checked} {graph : Graph program.base}
  {headers : Headers graph} {templates : Templates program} {views : Views templates}
  {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
  {authenticated : SourceCoreCallablePairedReadViews.Authenticated views world store value}
  {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}

theorem original_closure (restored : Read headers authenticated ledger) :
    restored.source = .instantiated restored.recipe.read.substitution restored.recipe.read.witnesses
      (.closure restored.recipe.applied.parameters restored.recipe.applied.resultType restored.recipe.applied.body
        restored.recipe.lexical.metadata.source restored.recipe.lexical.metadata.owner restored.captures.environment
        restored.header.principal.context.evidence) := restored.exact

theorem capture_order (restored : Read headers authenticated ledger) :
    restored.captures.environment.map Prod.fst = authenticated.underlying.template.source.scope.map Prod.fst := restored.captures.binders

end Read
end Solcore.Frontend.SourceCoreCallablePairedRestoration
