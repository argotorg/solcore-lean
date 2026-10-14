import Solcore.SourceSemantics.CoreLowering.AcceptedCoercedDirectExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCoercedClosureAdmission

/-! Flat original call metadata and leaf argument forms. The profile contains
no recursive expression grammar; the accepted action supplies its children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompilerCoercedExpressionProfile
open Core Frontend SourceInference
open AcceptedNamedExpressionFlow (LeafForm)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedPrimitiveSourceAdmission (nativeMetadata?)

def LeafAt (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧ LeafForm node.form

def leaf? (source : TypedSource) (id : ExpressionId) : Option (PLift (LeafAt source id)) := do
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .reference name (.local binder) =>
      pure ⟨node, found, form ▸ LeafForm.read name binder⟩
    | .reference name (.builtinBoolean value) =>
      pure ⟨node, found, form ▸ LeafForm.literal (.bool name value)⟩
    | .literal value => pure ⟨node, found, form ▸ LeafForm.literal (.word value)⟩
    | .integerLiteral value resolution =>
      pure ⟨node, found, form ▸ LeafForm.literal (.integer value resolution)⟩
    | .tuple [] => pure ⟨node, found, form ▸ LeafForm.literal .unit⟩
    | _ => none

private def allLeaves? (source : TypedSource) :
    (ids : List ExpressionId) → Option (PLift (∀ id ∈ ids, LeafAt source id))
  | [] => some ⟨by intro id member; cases member⟩
  | id :: ids => do
    let ⟨head⟩ ← leaf? source id
    let ⟨tail⟩ ← allLeaves? source ids
    pure ⟨by
      intro child member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail child member⟩

structure Profile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) (expression : ExpressionId) where
  node : ExpressionNode
  callee : ExpressionId
  arguments : List ExpressionId
  instantiation : DeclarationInstantiation
  found : source.lookupExpression? expression = some node
  form : node.form = .call callee arguments (.declaration instantiation)
  coercions : node.coercions ≠ []
  requirements : node.requirements ≠ []
  children : ∀ argument ∈ arguments, LeafAt source argument
  initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  direct : DirectSite rows instantiation
  metadataAccepted : ∃ receipt, nativeMetadata? compiled.indexed named source = some receipt

def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) (expression : ExpressionId) :
    Option (Profile compiled named source rows expression) := do
  match metadataAccepted : nativeMetadata? compiled.indexed named source with
  | none => none
  | some receipt =>
    match found : source.lookupExpression? expression with
    | none => none
    | some node =>
      match form : node.form with
      | .call callee arguments (.declaration instantiation) =>
        if coercions : node.coercions ≠ [] then
          if requirements : node.requirements ≠ [] then do
            let ⟨children⟩ ← allLeaves? source arguments
            if initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
                decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                  binding.initializer = expression)) = none then do
              let ⟨direct⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation
              pure ⟨node, callee, arguments, instantiation, found, form, coercions, requirements,
                children, initializer, direct, receipt, metadataAccepted⟩
            else none
          else none
        else none
      | _ => none

theorem Profile.metadata {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
    {rows : List SourceSpecialization.SpecializedFunction} {expression : ExpressionId}
    (profile : Profile compiled named source rows expression) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed named source (fun _ => False) := by
  obtain ⟨⟨metadata⟩, _⟩ := profile.metadataAccepted
  exact metadata

end Solcore.SourceSemantics.CoreLowering.CompilerCoercedExpressionProfile
