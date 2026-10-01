import Solcore.Frontend.SourceCoreCompatibleDataPlaces
import Solcore.Frontend.SourceCoreDataPlaceFaultSites

/-! Missing defaults reserve disjoint program-wide word ranges. Within one
range the actual raw mapping-header ID selects `typeMismatch rawValueType none`.
Input registry extensions use the same static range inventory; rebuilding the
diagnostic table performs metadata lookup only. It does not evaluate source.

The emitted code adds a header ID to the site's base. Preparation checks the
end of each reserved range without wrapping. Tables reject IDs outside the
reserved registry budget and headers of an unrelated runtime value type. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
open SourceInference
abbrev Context := SourceCoreCompatibleValues.Context
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Site := SourceCoreElaboration.ErrorSite
abbrev Diagnostic := SourceCoreFaultSites.Diagnostic

structure MissingSite where
  owner : Key
  site : Site
  binder : Option Resolved.LocalId
  keyType : TypeSystem.Ty
  valueType : TypeSystem.Ty
  span : Syntax.SourceSpan
  base : Core.Word
  deriving Repr

structure Program (context : Context) where
  program : SourceCoreDataPlaceFaultSites.Program
  missing : List MissingSite
  /-- The preexisting read/assignment/function boundary and place faults. -/
  fixed : List (Core.Word × Diagnostic)
  /-- Later diagnostic inventories start here, even before dynamic headers
  occupy the remaining slots in the reserved ranges. -/
  nextReason : Nat

def Program.context {context : Context} (_program : Program context) : Context := context

inductive Error where
  | base (error : SourceCoreProgramFaultSites.Error)
  | lowering (error : SourceCoreBasic.Error)
  | duplicateOccurrence (expression : ExpressionId)
  | ownerMismatch (expression : ExpressionId)
  | sourceOwnerMismatch (expected actual : Resolved.DeclarationId)
  | reasonSpaceExhausted
  | registryBudgetExceeded
  | registryOwnerMismatch
  deriving Repr

private def word (number : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? number with
  | some value => pure value | none => throw .reasonSpaceExhausted

/-- The native addition has the same number as the metadata decoder when
the reserved endpoint and authenticated header remain within their budget. -/
theorem token_nonWrapping (base header : Core.Word) (capacity : Nat)
    (reserved : base.val + capacity < Core.wordModulus) (bounded : header.val ≤ capacity) :
    (base.add header).val = base.val + header.val := by
  change (base.val + header.val) % Core.wordModulus = base.val + header.val
  apply Nat.mod_eq_of_lt
  omega

theorem token_ranges_disjoint (left right leftHeader rightHeader : Core.Word) (leftCapacity rightCapacity : Nat)
    (leftReserved : left.val + leftCapacity < Core.wordModulus)
    (rightReserved : right.val + rightCapacity < Core.wordModulus)
    (leftBounded : leftHeader.val ≤ leftCapacity) (rightBounded : rightHeader.val ≤ rightCapacity)
    (separate : left.val + leftCapacity < right.val) :
    left.add leftHeader ≠ right.add rightHeader := by
  intro same
  have equal := congrArg Fin.val same
  rw [token_nonWrapping left leftHeader leftCapacity leftReserved leftBounded,
    token_nonWrapping right rightHeader rightCapacity rightReserved rightBounded] at equal
  omega

private def targets (node : StatementNode) : List AssignmentResolution :=
  match node.form with
  | .assignValue assignment _ _ | .assignBitNot assignment => [assignment]
  | .forLoop initial _ post _ => (initial ++ post).filterMap fun
      | .assignValue assignment _ _ | .assignBitNot assignment => some assignment
      | _ => none
  | _ => []

/-- Raw headers are interpreted within the exact owning registry. The list
contains only headers compatible with this site's projected value type. -/
def missingDiagnostics (registry : SourceCoreRawMetadata.Registry)
    (sites : List MissingSite) : Except Error (List (Core.Word × Diagnostic)) := do
  unless registry.length ≤ registry.limits.maxEntries do throw .registryBudgetExceeded
  let mut diagnostics := []
  for site in sites do
    for (metadata, index) in registry.entries.zipIdx do
      match metadata with
      | .mapping keyType valueType =>
          if SourceCoreRawMetadata.runtimeType keyType = SourceCoreRawMetadata.runtimeType site.keyType &&
              SourceCoreRawMetadata.runtimeType valueType = SourceCoreRawMetadata.runtimeType site.valueType then
            let reason ← word (site.base.val + index + 1)
            unless diagnostics.any (fun previous => decide (previous.1 = reason)) do
              diagnostics := diagnostics ++ [(reason, {
                error := .typeMismatch valueType none, site := site.site, span := some site.span })]
      | _ => pure ()
  pure diagnostics

/-- Rebuild exact raw-type diagnostics after authenticated input extension.
The old static registry must remain a prefix; no slot is silently rebound. -/
def Program.tableForRegistry {context : Context} (program : Program context) (registry : SourceCoreRawMetadata.Registry)
    (_extension : SourceCoreRawMetadata.Extends program.context.registry registry) :
    Except Error SourceCoreFaultSites.Table := do
  let extra ← missingDiagnostics registry program.missing
  pure { program.program.rootTable with additional := program.fixed ++ extra }

def Program.diagnostic? {context : Context} (program : Program context) (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends program.context.registry registry)
    (reason : Core.Word) : Except Error (Option Diagnostic) := do
  let table ← program.tableForRegistry registry extension
  pure (table.diagnostic? reason)

/-- The base inventory has the same provider interface as the strict
DataPlaceFaultSites.Program. Only missing-default reasons represent ranges. -/
def prepare (context : Context) (plan : Plan) (root : Key)
    (extraSources : List (Key × TypedSource) := []) : Except Error (Program context) := do
  let base ← (SourceCoreProgramFaultSites.prepare plan root).mapError Error.base
  let used := base.rootTable.reads.map (·.reason.val) ++
    base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val]
  let mut next := used.foldl max 0 + 1
  let width := context.registry.limits.maxEntries + 1
  let mut indices : List SourceCoreDataFaultSites.IndexSite := []
  let mut places : List SourceCoreDataPlaceFaultSites.Site := []
  let mut missing : List MissingSite := []
  let mut fixed := base.rootTable.additional
  let sources := plan.specializations.map (fun specialized => (specialized.key, specialized.function.typedBody)) ++ extraSources
  for (owner, source) in sources do
    if source.owner ≠ owner.declaration then throw (.sourceOwnerMismatch owner.declaration source.owner)
    let mut seenIndices : List ExpressionId := []
    for retained in source.nodes do
      match retained with
      | .expression node =>
          match node.form with
          | .index mapping key =>
              if node.id.occurrence.owner ≠ source.owner then throw (.ownerMismatch node.id)
              if mapping.occurrence.owner ≠ source.owner then throw (.ownerMismatch mapping)
              if key.occurrence.owner ≠ source.owner then throw (.ownerMismatch key)
              if seenIndices.contains node.id then throw (.duplicateOccurrence node.id)
              seenIndices := node.id :: seenIndices
              let reason ← match indices.find? (fun previous => decide (previous.owner = owner ∧ previous.expression = node.id)) with
                | some previous => pure previous.reason
                | none => do
                    let reason ← word next
                    discard <| word (next + width - 1)
                    next := next + width
                    let diagnostic : Diagnostic := {
                      error := .typeMismatch node.type none, site := .occurrence node.id.occurrence, span := some node.span }
                    indices := indices ++ [⟨owner, node.id, reason, diagnostic⟩]
                    pure reason
              let baseNode ← match source.lookupExpression? mapping with
                | some base => pure base | none => throw (.lowering (.missingExpression mapping))
              let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
                | .mapping keyType valueType => pure (keyType, valueType)
                | _ => throw (.lowering (.missingExpression key))
              unless SourceCoreRawMetadata.runtimeType node.type = valueType do
                throw (.lowering (.missingExpression node.id))
              missing := missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩]
          | _ => pure ()
      | .statement node =>
          let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
          for assignment in targets node do
            -- Principal local bodies are visited again through their actual
            -- contextual instances. Only concrete routes generate code.
            let declared := (SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
              decide (binder.id = assignment.target.root))
            let concrete := SourceCoreDataCatalog.closed assignment.target.type &&
              declared.any (fun binder => SourceCoreDataCatalog.closed binder.scheme.body)
            if concrete then
              let route ← (SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source site assignment)
                |>.mapError Error.lowering
              unless route.steps.isEmpty || places.any (fun previous => decide
                  (previous.owner = owner ∧ previous.location = site ∧
                   previous.binder = assignment.target.root ∧ previous.missingType = none)) do
                let reason ← word next
                next := next + 1
                let diagnostic : Diagnostic := {error := .invalidPlaceProjection, site, span := some node.span}
                places := places ++ [⟨owner, site, assignment.target.root, none, reason, diagnostic⟩]
                fixed := fixed ++ [(reason, diagnostic)]
              for step in route.steps do
                match step with
                | .index _ key valueType =>
                    let reason ← match places.find? (fun previous => decide
                        (previous.owner = owner ∧ previous.location = site ∧
                         previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
                      | some previous => pure previous.reason
                      | none => do
                          let reason ← word next
                          discard <| word (next + width - 1)
                          next := next + width
                          let diagnostic : Diagnostic := {error := .typeMismatch valueType none, site, span := some node.span}
                          places := places ++ [⟨owner, site, assignment.target.root, some valueType, reason, diagnostic⟩]
                          pure reason
                    let keyNode ← match source.lookupExpression? key with
                      | some keyNode => pure keyNode | none => throw (.lowering (.missingExpression key))
                    missing := missing ++ [⟨owner, site, some assignment.target.root, keyNode.type, valueType, node.span, reason⟩]
                | _ => pure ()
  let extra ← missingDiagnostics context.registry missing
  let rootTable := {base.rootTable with additional := fixed ++ extra}
  let expressions : SourceCoreDataFaultSites.Program := {base, indices, rootTable}
  let program : SourceCoreDataPlaceFaultSites.Program := {base, expressions, places, rootTable}
  pure {program, missing, fixed, nextReason := next}

end Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
