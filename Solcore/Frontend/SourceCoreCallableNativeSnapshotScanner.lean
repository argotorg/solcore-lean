import Solcore.Frontend.SourceCoreLambdaTemplates

/-! Shared syntax inspection for snapshot-bearing native lambda templates.
The parser retains exact complete emission and manifest equations, actual
native body/capture indices and the sealed manifest receipt. It does not own a
compiler artifact, authenticate a runtime value, or infer source execution
history. Profile-specific caches must retain their actual compiler equation. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeSnapshotScanner
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Scope := SourceCoreFunctions.Scope

/-- A syntax strategy only. Its use in an owned compiler pass is certified
by the enclosing artifact cache, never by this public parameter alone. -/
structure Profile where
  frameType : Ty
  body : Word → Nat → Ty → Ty → Expr → Expr

def Profile.snapshotLambda (profile : Profile) (origin : Word) (referenceIndex : Nat)
    (parameter result : Ty) (rawBody : Expr) : Expr :=
  .letE (.loadCell (.var referenceIndex))
    (.lambda parameter (LanguageResult.resultType result)
      (profile.body origin referenceIndex parameter result rawBody))

inductive Error where
  | exhausted
  | malformedSnapshot
  | template (error : SourceCoreLambdaTemplates.Error)
  | manifestDepthMismatch
  | descriptorMismatch
  deriving Repr

private def removeInsertion (cutoff : Nat) (expression : Expr) : Expr :=
  expression.rename (fun index => if cutoff ≤ index then index - 1 else index)

/-- Extract only the body operand, without trusting the rest of the wrapper.
The complete snapshot expression is independently reconstructed below. -/
private def frameBody? : Expr → Option Expr
  | .letE _ (.letE _ (.letE body (.letE _ (.var 1)))) => some body
  | _ => none

private def captureIndices? : Scope → Expr → Option (List Nat)
  | [], .unit => some []
  | [_], .var index => some [index]
  | _ :: next :: rest, .pair (.var index) tail => (captureIndices? (next :: rest) tail).map (index :: ·)
  | _, _ => none

structure Template (profile : Profile) where private mk ::
  source : SourceCoreLambdaTemplates.Receipt
  creationReferenceIndex : Nat
  parameter : Ty
  result : Ty
  rawBody : Expr
  body : Expr
  carrier : Expr
  /-- Snapshot is the first value in the saved native closure environment. -/
  snapshotIndex : Nat := 0
  /-- Context reference follows the added snapshot in the saved environment. -/
  contextIndex : Nat
  /-- Manifest initialization runs under two withFrame binders and raw arg0.
  Snapshot belongs to the saved environment and is not subtracted here. -/
  manifestDepth : Nat := 3
  manifestIndices : List Nat
  references : List Nat
  nativeExact : carrier = .pair (.pair (.inLeft .word .unit)
    (.letE (.loadCell (.var creationReferenceIndex)) (.lambda parameter (LanguageResult.resultType result) body)))
    (.word source.lambda.descriptor)
  carrierExact : carrier = .pair (.pair (.inLeft .word .unit)
    (profile.snapshotLambda source.lambda.descriptor creationReferenceIndex parameter result rawBody))
    (.word source.lambda.descriptor)
  parameterExact : parameter = source.parameterType
  resultExact : result = source.resultType
  referenceExact : references = source.references.map (· + 1)
  manifestExact : references = manifestIndices.map (· - manifestDepth)
  snapshotExact : snapshotIndex = 0
  contextExact : contextIndex = creationReferenceIndex + 1

/-- Exact native body, including the lexical snapshot and restoration protocol.
The inverse scanner never supplies this equation from a manifest word alone. -/
theorem Template.bodyExact {profile : Profile} (template : Template profile) :
    template.body = profile.body template.source.lambda.descriptor
      template.creationReferenceIndex template.parameter template.result template.rawBody := by
  have exact := template.nativeExact.symm.trans template.carrierExact
  simpa only [Profile.snapshotLambda, Expr.pair.injEq, Expr.letE.injEq,
    Expr.lambda.injEq, and_self, true_and, and_true] using exact

def decode {checked : Checked} (inventory : SourceCoreLambdaTemplates.Inventory checked)
    (profile : Profile) (carrier : Expr) : Except Error (Template profile) := do
  let .pair (.pair identity payload) (.word descriptor) := carrier | throw .malformedSnapshot
  if identity != .inLeft .word .unit then throw .malformedSnapshot
  let .letE (.loadCell (.var referenceIndex)) (.lambda parameter (.sum .word result) body) := payload
    | throw .malformedSnapshot
  let shiftedBody ← match frameBody? body with | some body => pure body | none => throw .malformedSnapshot
  let rawBody := removeInsertion 1 (removeInsertion 0 (removeInsertion 0 shiftedBody))
  if payload != profile.snapshotLambda descriptor referenceIndex parameter result rawBody then
    throw .malformedSnapshot
  let source ← (SourceCoreLambdaTemplates.decode inventory
    (.pair (.pair identity (.lambda parameter (LanguageResult.resultType result) rawBody)) (.word descriptor)))
    |>.mapError Error.template
  let .letE (.pair (.word actual) (.pair _ captures)) _ := shiftedBody | throw .malformedSnapshot
  if actual != descriptor then throw .descriptorMismatch
  let manifestIndices ← match captureIndices? source.scope captures with
    | some indices => pure indices | none => throw .malformedSnapshot
  if manifestIndices.any (· < 4) then throw .manifestDepthMismatch
  let references := source.references.map (· + 1)
  if manifestExact : references = manifestIndices.map (· - 3) then
    if types : parameter = source.parameterType ∧ result = source.resultType then
      if carrierExact : carrier = .pair (.pair (.inLeft .word .unit)
          (profile.snapshotLambda source.lambda.descriptor referenceIndex parameter result rawBody))
          (.word source.lambda.descriptor) then
        if nativeExact : carrier = .pair (.pair (.inLeft .word .unit)
            (.letE (.loadCell (.var referenceIndex)) (.lambda parameter (LanguageResult.resultType result) body)))
            (.word source.lambda.descriptor) then
          pure ⟨source, referenceIndex, parameter, result, rawBody, body, carrier, 0,
            referenceIndex + 1, 3, manifestIndices, references, nativeExact, carrierExact, types.1, types.2, rfl, manifestExact, rfl, rfl⟩
        else throw .descriptorMismatch
      else throw .descriptorMismatch
    else throw .malformedSnapshot
  else throw .manifestDepthMismatch

private def snapshotShape : Expr → Bool
  | .letE (.loadCell (.var _)) (.lambda _ _ body) => (frameBody? body).isSome
  | _ => false

mutual
  def scan {checked : Checked} (inventory : SourceCoreLambdaTemplates.Inventory checked) (profile : Profile) : Nat → Expr → Except Error (List (Template profile))
    | 0, _ => .error .exhausted
    | fuel + 1, expression => do
      match expression with
      | .pair (.pair identity payload) descriptor =>
        if snapshotShape payload then
          let template ← decode inventory profile expression
          -- Recurse through actual native binders, never the inverse-renamed
          -- synthetic source template. Child capture slots depend on them.
          pure (template :: (← scan inventory profile fuel template.body))
        else pure ((← scan inventory profile fuel (.pair identity payload)) ++ (← scan inventory profile fuel descriptor))
      | .letE (.loadCell (.var _)) (.lambda _ _ body) =>
        if (frameBody? body).isSome then throw .malformedSnapshot
        scan inventory profile fuel body
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure []
      | .lambda _ _ body => scan inventory profile fuel body
      | .pair left right | .apply left right | .storeCell left right | .binary _ left right | .letE left right =>
        pure ((← scan inventory profile fuel left) ++ (← scan inventory profile fuel right))
      | .first operand | .second operand | .loadCell operand | .inLeft _ operand | .inRight _ operand |
        .newCell _ operand | .construct _ operand | .unary _ operand => scan inventory profile fuel operand
      | .caseE first second third | .ifE first second third | .ternary _ first second third =>
        pure ((← scan inventory profile fuel first) ++ (← scan inventory profile fuel second) ++ (← scan inventory profile fuel third))
      | .matchData _ _ scrutinee branches => pure ((← scan inventory profile fuel scrutinee) ++ (← scanBranches inventory profile fuel branches))
  def scanBranches {checked : Checked} (inventory : SourceCoreLambdaTemplates.Inventory checked) (profile : Profile) : Nat → List Expr → Except Error (List (Template profile))
    | _, [] => pure []
    | 0, _ :: _ => .error .exhausted
    | fuel + 1, head :: tail => do pure ((← scan inventory profile fuel head) ++ (← scanBranches inventory profile fuel tail))
end


end Solcore.Frontend.SourceCoreCallableNativeSnapshotScanner
