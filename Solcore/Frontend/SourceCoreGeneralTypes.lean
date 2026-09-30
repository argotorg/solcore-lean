import Solcore.Frontend.SourceCoreFunctions
import Solcore.Frontend.SourceCoreDataExpressions

/-! Authenticated metadata projection for the closed data catalog. This profile
shares function traversal with the existing scalar profile. Binder and place
checks remain separate from source-value authentication at the public boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreGeneralTypes

open SourceInference
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error

def projectType (checked : Checked) (site : SourceCoreElaboration.ErrorSite)
    (type : TypeSystem.Ty) : Except Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError
    (fun _ => .typeProjection ⟨site, .unsupportedType type⟩)

def readStatement (checked : Checked) (source : TypedSource) (id : StatementId) :
    Except Error (StatementNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupStatement? id with
    | some node => pure node
    | none => throw (.missingStatement id)
  pure (node, ← projectType checked (.occurrence id.occurrence) node.type)

def lowerBinder (checked : Checked) (source : TypedSource) (scope : Scope)
    (binder : TypedBinder) : Except Error Core.Ty := do
  if binder.id.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding binder.id)
  unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent binder.id)
  if binder.comptime && !checked.catalog.callableContracts then throw (.comptimeBinding binder.id)
  if scope.any (fun entry => decide (entry.1 = binder.id)) then throw (.duplicateBinding binder.id)
  projectType checked (.binder binder.id) binder.scheme.body

def lowerAssignment (checked : Checked) (source : TypedSource) (scope : Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) : Except Error (Nat × Core.Ty) := do
  if operator ≠ .equal then throw (.unsupportedAssignmentOperator operator)
  let binder := assignment.target.root
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent binder)
  unless assignment.target.projections.isEmpty do throw (.projectedAssignment binder)
  let (index, type) ← match SourceCoreLocalCell.lookup? scope binder with
    | some entry => pure entry
    | none => throw (.missingBinding binder)
  let projected ← projectType checked (.binder binder) assignment.target.type
  SourceCoreBasic.ensureType (.binder binder) type projected
  pure (index, type)

def lowerRead (checked : Checked) (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reason : Core.Word) : Except Error Core.Expr := do
  let (node, type) ← SourceCoreDataExpressions.readExpression checked source id
  let binder ← match node.form with
    | .reference _ (.local binder) => pure binder
    | _ => throw (.unsupportedExpression id node.form)
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  let (index, payload) ← match SourceCoreLocalCell.lookup? scope binder with
    | some entry => pure entry
    | none => throw (.missingBinding binder)
  SourceCoreBasic.ensureType (.occurrence id.occurrence) type payload
  match SourceCoreDataCatalog.erase node.type with
  | .mapping key value =>
      let key ← projectType checked (.occurrence id.occurrence) key
      let value ← projectType checked (.occurrence id.occurrence) value
      let identity ← match checked.catalog.identity? node.type with
        | some identity => pure identity
        | none => throw (.unsupportedExpression id node.form)
      let layout : Core.OrderedMapping.Layout := ⟨key, value, identity⟩
      unless checked.catalog.definitions[identity.index]? = some layout.definition do
        throw (.unsupportedExpression id node.form)
      pure (SourceCoreDataExpressions.readMapping layout (.var index))
  | _ => pure (Core.OptionalCell.read payload (.var index) reason)

/-- Data leaves recurse through the owning function policy. Scalar leaves use
the established lowering after the shared metadata check. -/
def leafLowerer (checked : Checked) (signatures : ProgramSignatures)
    (child : SourceCoreFunctions.ExpressionLowerer) : SourceCoreFunctions.ExpressionLowerer :=
  fun fuel source scope id reasonAt => do
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    match node.form with
    | .constructor _ _ | .member _ _ _ | .proxy _ | .index _ _ =>
        SourceCoreDataExpressions.lowerWithReasons fuel checked signatures child source scope id reasonAt
    | .tuple elements =>
        let (_, type) ← SourceCoreDataExpressions.readExpression checked source id
        let lowered ← elements.mapM fun element => child fuel source scope element reasonAt
        let packed := SourceCoreCalls.packArguments lowered
        SourceCoreBasic.ensureType (.occurrence id.occurrence) type packed.type
        pure ⟨type, packed.expression⟩
    | _ => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)

def policy (checked : Checked) (signatures : ProgramSignatures) : SourceCoreFunctions.Policy := {
  projectType := projectType checked
  readExpression := SourceCoreDataExpressions.readExpression checked
  lowerBinder := lowerBinder checked
  lowerRead := lowerRead checked
  leafLowerer := leafLowerer checked signatures
}

end Solcore.Frontend.SourceCoreGeneralTypes
