import Solcore.Frontend.SourceCoreCallableIndexedReadViews
import Solcore.Frontend.SourceCoreCallablePairedHeaders

/-! Source closure restoration from the actual indexed callable profile.
Code authenticity and physical capture joins are supplied by the owning native
receipts. Constant-depth saved indices select raw lexical headers and exact read recipes;
restoration performs no source traversal, substitution or evidence resolution.

The output retains the original closure for an instantiated read. Produced and
stored wrappers keep the corresponding completion provenance. These receipts
establish the reconstruction boundary; full source execution meaning still
requires the enclosing native emission/history theorem.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedRestoration
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Headers := @SourceCoreCallablePairedHeaders.Prepared
abbrev Templates := @SourceCoreCallableIndexedTemplates.Cache
abbrev Views := @SourceCoreCallableIndexedReadViews.Cache
abbrev Ledger := @SourceCoreAllocationLedger.TypedLedger
abbrev SourceValue := SourceTypedRuntime.Value

inductive Error where
  | captures (error : SourceCoreCallableIndexedCaptures.Error)
  | lexicalUnavailable
  | callerUnavailable
  | lambdaHeaderUnavailable (position : Nat) (descriptor : Core.Word)
  | principalHeaderUnavailable (position : Nat) (binder : Resolved.LocalId)
  | readRecipeUnavailable (caller lexical : Nat) (view target : Core.Word)
  deriving Repr

structure Ordinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated ledger
  position : Nat
  lookup : authenticated.snapshot.frame.index? = some position
  header : SourceCoreCallablePairedHeaders.LambdaHeader graph headers.principals
  selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor = some header
  source : SourceValue
  exact : source = header.sourceValue captures.environment

def restoreOrdinary {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Ordinary headers authenticated ledger) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated ledger).mapError Error.captures
  match lookup : authenticated.snapshot.frame.index? with
  | some position =>
    match selected : headers.lambdaAt? position authenticated.template.source.lambda.descriptor with
    | none => throw (.lambdaHeaderUnavailable position authenticated.template.source.lambda.descriptor)
    | some header => pure ⟨captures, position, lookup, header, selected, header.sourceValue captures.environment, rfl⟩
  | _ => throw .lexicalUnavailable

structure Read {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : SourceCoreCallableIndexedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated.underlying ledger
  caller : Nat
  callerLookup : authenticated.caller.frame.index? = some caller
  lexical : Nat
  lexicalLookup : authenticated.underlying.snapshot.frame.index? = some lexical
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
    (authenticated : SourceCoreCallableIndexedReadViews.Authenticated views world store value)
    {initial : List SourceTypedRuntime.Cell} (ledger : Ledger program.layouts initial world store) :
    Except Error (Read headers authenticated ledger) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  match callerLookup : authenticated.caller.frame.index? with
  | some caller =>
    match lexicalLookup : authenticated.underlying.snapshot.frame.index? with
    | some lexical =>
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

/-- The original lexical declaration and saved source captures are retained. -/
theorem Ordinary.raw_closure {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {templates : Templates program} {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (restored : Ordinary headers authenticated ledger) :
    restored.source = .closure restored.header.parameters restored.header.resultType restored.header.body
      restored.header.state.metadata.source restored.header.state.metadata.owner restored.captures.environment
      restored.header.context.context.evidence := by
  rw [restored.exact]
  rfl

/-- A read value keeps its own caller substitution and original lexical source. -/
theorem Read.original_closure {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {templates : Templates program} {views : Views templates}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallableIndexedReadViews.Authenticated views world store value}
    {initial : List SourceTypedRuntime.Cell} {ledger : Ledger program.layouts initial world store}
    (restored : Read headers authenticated ledger) :
    restored.source = restored.recipe.applied.sourceValue restored.captures.environment
      restored.header.principal.context.evidence := restored.exact

end Solcore.Frontend.SourceCoreCallableIndexedRestoration
