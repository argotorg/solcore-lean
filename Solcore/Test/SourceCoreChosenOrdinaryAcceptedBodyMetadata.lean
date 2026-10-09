import Solcore.Test.SourceCoreChosenOrdinaryAcceptedFixture

/-! Finite static receipts from the unchanged accepted lambda fixture.
These checks retain actual statement projection and occurrence metadata.
Source typing and body execution remain separate judgments. -/
set_option autoImplicit false
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyMetadata
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SourceCoreChosenOrdinaryAcceptedFixture
open CallableIndexedNamedGeneration

/-- Reject match forms anywhere in the actual retained node table. -/
def checkNoMatches (view : TypedSource) : Bool :=
  view.nodes.all fun
    | .expression _ => true
    | .statement node => match node.form with
      | .matchWith _ => false
      | _ => true

/-- Read every expression's original retained output-coercion list. -/
def checkEmptyCoercions (view : TypedSource) : Bool :=
  view.nodes.all fun
    | .statement _ => true
    | .expression node => node.coercions.isEmpty

theorem no_matches_of_checked {view : TypedSource}
    (accepted : checkNoMatches view = true) :
    ∀ statement node, view.lookupStatement? statement = some node →
      ∀ resolution, node.form ≠ .matchWith resolution := by
  intro statement node found resolution same
  have member := (SourceSemantics.lookupStatement?_sound found).1
  have checked := List.all_eq_true.mp accepted (.statement node) member
  change (match node.form with | .matchWith _ => false | _ => true) = true at checked
  rw [same] at checked
  contradiction

theorem empty_coercions_of_checked {view : TypedSource}
    (accepted : checkEmptyCoercions view = true) :
    ∀ expression node, view.lookupExpression? expression = some node → node.coercions = [] := by
  intro expression node found
  have member := (SourceSemantics.lookupExpression?_sound found).1
  have checked := List.all_eq_true.mp accepted (.expression node) member
  change node.coercions.isEmpty = true at checked
  cases rows : node.coercions with
  | nil => rfl
  | cons _ _ => simp only [rows, List.isEmpty_cons, Bool.false_eq_true] at checked

/-- Static facts obtained by checking the actual node table and checked
projection; no compiler output, Source node or requirement is replaced. -/
structure Receipt (packet : Packet) (given : Graph packet) : Prop where
  noMatches : checkNoMatches (source packet.named) = true
  emptyCoercions : checkEmptyCoercions (source packet.named) = true
  inputs : packet.named.inputs = []
  projected : SourceCoreCompatibleDataExpressions.projectType packet.compiled.compatible.checked
    (.occurrence (statementId packet 2).occurrence) given.returned.type = .ok .word

/-- Each successful finite check retains its original equation. -/
def receipt (packet : Packet) (given : Graph packet) : Except String (PLift (Receipt packet given)) := do
  if noMatches : checkNoMatches (source packet.named) = true then
    if emptyCoercions : checkEmptyCoercions (source packet.named) = true then
      if noInputs : packet.named.inputs.isEmpty = true then
        have inputs : packet.named.inputs = [] := by
          cases rows : packet.named.inputs with
          | nil => rfl
          | cons _ _ => simp only [rows, List.isEmpty_cons, Bool.false_eq_true] at noInputs
        match projected : SourceCoreCompatibleDataExpressions.projectType packet.compiled.compatible.checked
            (.occurrence (statementId packet 2).occurrence) given.returned.type with
        | .ok .word => pure ⟨⟨noMatches, emptyCoercions, inputs, projected⟩⟩
        | _ => throw "actual inner return projection differs from Word"
      else throw "actual named parameter list is nonempty"
    else throw "actual retained Source contains an output coercion"
  else throw "actual retained Source contains a match form"

theorem Receipt.no_matches {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    ∀ statement node, (source packet.named).lookupStatement? statement = some node →
      ∀ resolution, node.form ≠ .matchWith resolution :=
  no_matches_of_checked checked.noMatches

theorem Receipt.empty_coercions {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    ∀ expression node, (source packet.named).lookupExpression? expression = some node → node.coercions = [] :=
  empty_coercions_of_checked checked.emptyCoercions

/-- Original lookup and checked projection yield the real compatible read. -/
theorem Receipt.return_read {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    SourceCoreCompatibleDataExpressions.readStatement packet.compiled.compatible.checked
      (source packet.named) (statementId packet 2) = .ok (given.returned, .word) := by
  unfold SourceCoreCompatibleDataExpressions.readStatement
  have owner : (statementId packet 2).occurrence.owner = (source packet.named).owner := rfl
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [given.returnedFound]
  simp only [checked.projected, bind, Except.bind, pure, Except.pure]

/-- Empty compiler scope has no visible native binder needing a Source
local declaration; this retains the caller's actual declaration context. -/
theorem Receipt.initial_declarations {packet : Packet} {given : Graph packet}
    (checked : Receipt packet given) :
    CompatibleExpressionReads.ScopeDeclarations (source packet.named) (initialScope packet)
      (runtimeContext packet) := by
  intro binder declared index type found _root
  have scope : initialScope packet = [] := by
    simp only [initialScope, checked.inputs, List.reverse_nil, List.map_nil]
  rw [scope] at found
  cases found

/-- A real finite consumer of the retained compiler/metadata fixture. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match receipt fixture.packet fixture.graph with
    | .error error => throw (IO.userError error)
    | .ok _ => IO.println "accepted literal body metadata: original return projection, no match forms and empty output coercions checked"

end Tests.SourceCoreChosenOrdinaryAcceptedBodyMetadata
