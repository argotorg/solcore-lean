import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyStopping

/-! Raw completion inspection distinguishes function tails from nested discarded
values. Stopped blocks and conditionals retain their original finite receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion
open Frontend SourceInference ScopedSourceBodyStopping

/-- This inspection is bounded by the original occurrence table. A successful
result retains the complete finite stopping proof. -/
def stopped? (source : TypedSource) (statements : List StatementId) :=
  returnStopped? source (source.nodes.length + 1) statements

def Stops (source : TypedSource) (statements : List StatementId) : Prop :=
  (stopped? source statements).isSome = true

instance (source : TypedSource) (statements : List StatementId) : Decidable (Stops source statements) :=
  inferInstanceAs (Decidable ((stopped? source statements).isSome = true))

theorem Stops.original {source statements} (stops : Stops source statements) :
    ReturnStopped source statements := by
  unfold Stops at stops
  cases found : stopped? source statements with
  | none => simp [found] at stops
  | some proof => exact proof.down

/-- Only a true-mode final expression supplies a function result. -/
def notTail (mode : Bool) (_rest : List StatementId) : StatementForm → Bool
  | .expression _expression semicolon => semicolon || !mode
  | _ => true

def matchStops (source : TypedSource) (resolution : MatchResolution) : Bool :=
  resolution.cases.all (fun arm => (stopped? source arm.body).isSome) &&
    (resolution.defaultBody.any (fun statements => (stopped? source statements).isSome))

/-- The emitted outer suffix excludes nonfinal bare values in function mode.
Direct transfers omit their remaining roots, exactly as the compiler does. -/
def stopsHere : StatementForm → Bool
  | .returnStmt _ | .breakStmt | .continueStmt => true
  | _ => false

def tailForms? (source : TypedSource) : Bool → List StatementId → Bool
  | false, _ => true
  | true, [] => true
  | true, id :: rest =>
      match source.lookupStatement? id with
      | none => false
      | some node =>
          if stopsHere node.form then true else
          match node.form with
          | .expression _ false => rest.isEmpty
          | _ => tailForms? source true rest

def TailForms (source : TypedSource) (mode : Bool) (statements : List StatementId) : Prop :=
  tailForms? source mode statements = true

instance (source : TypedSource) (mode : Bool) (statements : List StatementId) :
    Decidable (TailForms source mode statements) := inferInstanceAs (Decidable (_ = true))

theorem TailForms.tail {source mode id node rest}
    (forms : TailForms source mode (id :: rest))
    (found : source.lookupStatement? id = some node)
    (continues : stopsHere node.form = false) : TailForms source mode rest := by
  cases mode with
  | false => simp [TailForms, tailForms?]
  | true =>
    cases form : node.form <;> simp_all [TailForms, tailForms?, stopsHere]
    rename_i expression semicolon
    cases semicolon with
    | true => exact forms
    | false => cases rest <;> simp_all [tailForms?]

theorem TailForms.discard_mode {source mode id node expression rest}
    (forms : TailForms source mode (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (notFinal : (mode && rest.isEmpty) = false) : mode = false := by
  cases mode with
  | false => rfl
  | true => simp [TailForms, tailForms?, found, form, stopsHere] at forms; simp [forms] at notFinal

inductive Finish (source : TypedSource) (expected : TypeSystem.Ty) :
    Bool → List StatementId → Prop where
  | nested (statements) : Finish source expected false statements
  | empty (unit : expected = .unit) : Finish source expected true []
  | returning {id node value rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt value) : Finish source expected true (id :: rest)
  | tail {id node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression false) (type : node.type = expected) :
      Finish source expected true [id]
  | prefix {id node rest} (found : source.lookupStatement? id = some node)
      (continuing : notTail true rest node.form = true)
      (remaining : Finish source expected true rest) : Finish source expected true (id :: rest)
  | block {id node body rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .block body) (stopped : Stops source body)
      (tailForms : TailForms source true rest) :
      Finish source expected true (id :: rest)
  | matching {id node resolution fallback rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (present : resolution.defaultBody = some fallback)
      (arms : resolution.cases.all (fun arm => (stopped? source arm.body).isSome) = true)
      (default : Stops source fallback) (tailForms : TailForms source true rest) : Finish source expected true (id :: rest)
  | conditional {id node condition left right rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen condition left (some right))
      (first : Stops source left) (second : Stops source right)
      (tailForms : TailForms source true rest) :
      Finish source expected true (id :: rest)

theorem Finish.forms {source expected mode statements}
    (finish : Finish source expected mode statements) : TailForms source mode statements := by
  induction finish with
  | nested => simp [TailForms, tailForms?]
  | empty => rfl
  | returning found form => simp [TailForms, tailForms?, found, form, stopsHere]
  | tail found form type => simp [TailForms, tailForms?, found, form, stopsHere]
  | @«prefix» id node rest found continuing remaining ih =>
    cases form : node.form <;>
      simp_all [TailForms, tailForms?, notTail, stopsHere]
  | block found form stopped tailForms => simpa [TailForms, tailForms?, found, form, stopsHere] using tailForms
  | matching found form present arms default tailForms => simpa [TailForms, tailForms?, found, form, stopsHere] using tailForms
  | conditional found form first second tailForms => simpa [TailForms, tailForms?, found, form, stopsHere] using tailForms

/-- Completion is checked at the original raw result, before native projection.
The remaining statement profile checks all visited operands and binders. -/
def finish? (source : TypedSource) (expected : TypeSystem.Ty) :
    (mode : Bool) → (statements : List StatementId) → Option (PLift (Finish source expected mode statements))
  | false, statements => some ⟨.nested statements⟩
  | true, [] => if unit : expected = .unit then some ⟨.empty unit⟩ else none
  | true, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      let next := do
        if continuing : notTail true rest node.form = true then
          let ⟨remaining⟩ ← finish? source expected true rest
          pure ⟨Finish.prefix found continuing remaining⟩
        else none
      match form : node.form with
      | .returnStmt _ => some ⟨.returning found form⟩
      | .expression expression false =>
        match restEq : rest with
        | [] => if type : node.type = expected then some ⟨.tail found form type⟩ else none
        | _ :: _ => by simpa only [restEq] using next
      | .block body =>
        if stops : Stops source body then
          if tailForms : TailForms source true rest then some ⟨.block found form stops tailForms⟩ else none
        else next
      | .matchWith resolution =>
        match present : resolution.defaultBody with
        | none => next
        | some fallback =>
          if arms : resolution.cases.all (fun arm => (stopped? source arm.body).isSome) = true then
            if default : Stops source fallback then
              if tailForms : TailForms source true rest then some ⟨.matching found form present arms default tailForms⟩ else none
            else next
          else next
      | .ifThen condition left (some right) =>
        if first : Stops source left then
          if second : Stops source right then
            if tailForms : TailForms source true rest then some ⟨.conditional found form first second tailForms⟩ else none
          else next
        else next
      | _ => next

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion
