import Solcore.SourceSemantics.CoreLowering.ForHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.ForPostMeaning

/-! Actual default header acceptance reconstructs binder context extensions,
a later assignment/read of that binder, and the static normal endpoint. -/

set_option autoImplicit false

namespace Tests.SourceCoreForHeaderCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"for_header_certificate", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "for_header_certificate.solc" }, startByte := 0, endByte := 1 }
private def falseNode : ExpressionNode := { id := exprId 0, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def readNode : ExpressionNode := { id := exprId 1, span, type := .bool, form := .reference "flag" (.local binder.id) }
private def source : TypedSource := { owner, nodes := [.expression falseNode, .expression readNode], roots := [], inputs := [] }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def reason : Core.Word := Core.Word.ofNatModulo 73
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def items : List ForItemForm := [
  .letDecl binder (some (exprId 0)), .assignValue assignment .equal (exprId 0), .expression (exprId 1)]
private def code : Core.Expr := Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .unit) .bool
  (Core.LanguageResult.success (.bool false))
  (Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 0) (Core.LanguageResult.success (.bool false))
    (Core.LocalSequence.discard (Core.LocalLoop.controlType .unit) (Core.OptionalCell.read .bool (.var 0) reason)
      (Core.LocalLoop.fallthrough .unit)))

private theorem accepted : SourceCoreLoops.lowerForItems (LoopStatements.Default.defaultPolicy compilation)
    (.declaration owner) 10 source [] items .unit (fun _ => reason)
    (fun _ => .ok (Core.LocalLoop.fallthrough .unit)) = .ok code := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private theorem certificate : ForHeaders.Tree compilation source (fun _ => reason) .unit
    (ForHeaders.Fallthrough .unit) [] context items code :=
  ForHeaders.tree_of_lowerPost (BasicStatements.ScopeContextAligned.empty signatures) unique accepted

example : Core.HasType [] code (Core.LocalLoop.resultType .unit) := by
  apply certificate.hasType .unit
  intro scope context code endpoint
  cases endpoint
  exact Core.LocalLoop.fallthrough_hasType .unit

example (result : Core.Expr)
    (accepted : SourceCoreLoops.lowerForItems (LoopStatements.Default.defaultPolicy compilation)
      (.declaration owner) 10 source [] items .unit (fun _ => reason)
      (fun _ => .ok (Core.LocalLoop.fallthrough .unit)) = .ok result) :
    ForHeaders.Tree compilation source (fun _ => reason) .unit (ForHeaders.Fallthrough .unit) [] context items result :=
  ForHeaders.tree_of_lowerPost (BasicStatements.ScopeContextAligned.empty signatures) unique accepted

private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible

/-- Header source execution and Core completion are constructed from static
compiler evidence and an empty represented initial state. -/
example (program : Program) :
    ForHeaders.PostResult program context [] source (fun _ => reason) [] ⟨[]⟩ items .unit [] [] [] [] code := by
  have layout : LoopStatements.Layout [] [] [] [] [] Core.Renaming.id :=
    ⟨Core.Renaming.respects_id [], fun found => found, .nil⟩
  simpa only [Core.Expr.rename_id] using certificate.construct_post program [] valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty layout

def run : IO Unit := do
  unless Core.runStateful 300 (.initial code [] []) ==
      .done (Core.LocalLoop.fallthroughValue .unit) [.inRight .unit (.bool false)] do
    throw (IO.userError "for-header initializer scope did not reach the assignment and read")

end Tests.SourceCoreForHeaderCertificates
