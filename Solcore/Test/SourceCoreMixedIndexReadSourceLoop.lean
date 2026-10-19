import Solcore.Test.SourceCoreMixedIndexReadSourceHeap

/-! Independent Source execution of the mapping initializer and the continue/post
path. Both writes rebuild the mapping in the exact current heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedIndexRead
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

theorem projected_key_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root : Resolved.LocalId} {key : ExpressionId} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context ⟨root,[.index key],.word⟩ type) :
    ∃ keyType, ExpressionHasType source context key keyType := by
  cases typed with
  | intro _ projections _ =>
    cases projections with | index key _ => exact ⟨_,key⟩

private theorem Shape.header_add {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (active : Bool) (suffix : List Dynamic.Cell) (old : Word)
    (key right : Tests.SourceCoreSelectedInterleavedLocal.WordNode source)
    (keyValue : key.resolution.rawValue = 3)
    (unique : NodeOccurrencesUnique source)
    (typed : SourceAssignmentHasType source context ⟨⟨shape.table.id,[.index key.node.id],.word⟩,[]⟩ .add right.node.id) :
    Dynamic.ForItemsExecute program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix)
      [.assignValue ⟨⟨shape.table.id,[.index key.node.id],.word⟩,[]⟩ .add right.node.id] context
      (phaseEnvironment shape base environment)
      (phaseHeap base (some (old.add (Word.ofNatModulo right.resolution.rawValue))) active suffix) := by
  cases typed with
  | wordCompound _ place rightTyped _ =>
    obtain ⟨_,keyTyped⟩ := projected_key_typed place
    have keyTrace := key.evaluates (program := program) evidence (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix) unique keyTyped
    rw [keyValue] at keyTrace
    have rightTrace := right.evaluates (program := program) evidence (phaseEnvironment shape base environment)
      (phaseHeap base (some old) active suffix) unique rightTyped
    exact .cons (.assignValue (projected_add (.tail shape.activeTable .head) keyTrace rightTrace)) .nil

def loopValue (flag : Bool) : Word := Word.ofNatModulo (if flag then 13 else 11)

private theorem Shape.loop_body {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (base : Dynamic.Heap) (environment : Dynamic.Environment) (value : Word) (suffix : List Dynamic.Cell) :
    Dynamic.StatementsExecute program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some value) true suffix) [shape.activeWrite.node.id,shape.continuing.node.id]
      context (.continuing (phaseEnvironment shape base environment))
      (phaseHeap base (some value) false suffix) := by
  have assigned := Dynamic.StatementExecutes.assignValue (program := program) (context := context)
    (evidence := evidence) (environment := phaseEnvironment shape base environment)
    (lookupStatement?_sound shape.activeWrite.found) shape.activeWrite.formEq
    (Dynamic.SourcePlaceAssignment.intro
      (.intro .head (phaseHeap.active base (some value) true suffix) .nil
        (phaseHeap.active base (some value) true suffix) .initialized .nil)
      (boolean_value shape.falseNode)
      (.intro (phaseHeap.active base (some value) true suffix) rfl .initialized
        (.leaf (.equal _ _)) (phaseHeap.write_active base (some value) true false suffix)))
  exact .cons assigned (.terminal
    (.continueStmt (lookupStatement?_sound shape.continuing.found) shape.continuing.formEq) (.continuing _))

theorem Shape.loop_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    (evidence : Dynamic.EvidenceEnvironment) (base : Dynamic.Heap) (environment : Dynamic.Environment)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context shape.loop.node.id final facts)
    (flag : Bool) (suffix : List Dynamic.Cell) :
    Dynamic.StatementExecutes program context evidence source (phaseEnvironment shape base environment)
      (phaseHeap base (some (Word.ofNatModulo 10)) flag suffix) shape.loop.node.id final
      (.fallthrough (phaseEnvironment shape base environment))
      (phaseHeap base (some (loopValue flag)) false suffix) := by
  have form := form_at unique shape.loop.found typed
  rw [shape.loop.formEq] at form
  cases form with
  | forLoop initial _ _ post =>
    cases initial with
    | cons initialized tail =>
      cases initialized with
      | assignValue initialTyped =>
        cases tail
        cases post with
        | cons postItem tail =>
          cases postItem with
          | assignValue postTyped =>
            have initialTrace := shape.header_add (program := program) evidence base environment flag suffix
              (Word.ofNatModulo 10) shape.initialKey shape.one shape.initialKeyValue unique initialTyped
            rw [shape.oneValue] at initialTrace
            have add1 : (Word.ofNatModulo 10).add (Word.ofNatModulo 1) = Word.ofNatModulo 11 := by decide
            rw [add1] at initialTrace
            apply Dynamic.StatementExecutes.forLoop (program := program) (evidence := evidence)
              (outcome := .fallthrough (phaseEnvironment shape base environment))
              (lookupStatement?_sound shape.loop.found) shape.loop.formEq initialTrace
            cases flag with
            | false => exact .done (read_value shape.guardRead (shape.active_stored base environment _ false suffix))
            | true =>
              have postTrace := shape.header_add (program := program) evidence base environment false suffix
                (Word.ofNatModulo 11) shape.postKey shape.two shape.postKeyValue unique postTyped
              rw [shape.twoValue] at postTrace
              have add2 : (Word.ofNatModulo 11).add (Word.ofNatModulo 2) = Word.ofNatModulo 13 := by decide
              rw [add2] at postTrace
              exact .nextContinue (read_value shape.guardRead (shape.active_stored base environment _ true suffix))
                (shape.loop_body _ evidence base environment _ suffix) postTrace
                (.done (read_value shape.guardRead (shape.active_stored base environment _ false suffix)))

end Tests.SourceCoreMixedIndexRead
