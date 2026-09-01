import Solcore.Syntax.Parser.BalancedBlockCaptureCompletenessProperties
import Solcore.Syntax.Parser.BalancedBlockCaptureSoundnessProperties
import Solcore.Syntax.Parser.CoreBlockSoundnessProperties
import Solcore.Syntax.Parser.IsolatedBlockDiagnosticReflectionProperties

/-!
Exact declarative soundness for balanced block isolation.

The direct branch retains the parent's active window.  The captured branch
runs the supplied block parser in the exact balanced child window and resumes
the parent at the matching closing brace.  A recovered child rejection cannot
produce a diagnostic-free successful result.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Diagnostic-free successful block isolation follows the exact declarative
direct-or-captured relation for any sound inner block parser.
-/
theorem isolateBlock_success_sound
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (parser : Parser Block)
    (parserSound : ∀ {input next : State} {body : Block},
      next.diagnosticsRev = [] →
      parser input = .ok body next →
      blockParses input.declarativeRemainder body
        next.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : isolateBlock parser input = .ok body next) :
    DeclarativeGrammar.IsolatedCoreBlockParses blockParses
      input.declarativeRemainder body next.declarativeRemainder := by
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact .direct
        (BlockInternals.captureBlock?_none_absent captureResult)
        (parserSound diagnosticFree result)
  | some captured =>
      simp only [captureResult] at result
      rcases BlockInternals.captureBlock?_success_sound captureResult with
        ⟨capture, captureParsed, spanEq, endIndexEq, endByteEq⟩
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | invariant error => simp [childResult] at result
      | reject failure childAfter =>
          simp only [childResult] at result
          cases result
          simp [State.mergeDiagnostics, State.emit] at diagnosticFree
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          have childDiagnosticFree : childAfter.diagnosticsRev = [] := by
            simp [State.mergeDiagnostics] at diagnosticFree
            exact diagnosticFree.1
          have childInputEq :
              State.declarativeRemainder
                  (input.enterWindow input.cursor captured.window) =
                capture.childRemainder input.declarativeRemainder := by
            simp [State.declarativeRemainder, State.enterWindow,
              DeclarativeGrammar.BalancedBlockCapture.childRemainder,
              endIndexEq]
          have parentOutputEq :
              State.declarativeRemainder
                  (State.mergeDiagnostics
                    ({ input with cursor := captured.window.endIndex } : State)
                    childAfter) =
                capture.parentRemainder input.declarativeRemainder := by
            simp [State.declarativeRemainder, State.mergeDiagnostics,
              DeclarativeGrammar.BalancedBlockCapture.parentRemainder,
              endIndexEq]
          rw [parentOutputEq]
          exact .captured captureParsed (by
            rw [← childInputEq]
            exact parserSound childDiagnosticFree childResult)

/--
The generic isolated-block contract packages exact declarative soundness with
backward diagnostic reflection from the supplied inner parser.
-/
theorem isolateBlock_success_sound_and_reflects
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (parser : Parser Block)
    (parserReflects : Parser.ReflectsDiagnosticFreeOnSuccess parser)
    (parserSound : ∀ {input next : State} {body : Block},
      next.diagnosticsRev = [] →
      parser input = .ok body next →
      blockParses input.declarativeRemainder body
        next.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : isolateBlock parser input = .ok body next) :
    DeclarativeGrammar.IsolatedCoreBlockParses blockParses
        input.declarativeRemainder body next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  exact ⟨isolateBlock_success_sound blockParses parser parserSound
      diagnosticFree result,
    isolateBlock_reflectsDiagnosticFreeOnSuccess parser parserReflects
      input body next result diagnosticFree⟩

/-- Exact declarative soundness for an isolated raw Core block. -/
theorem isolatedCoreBlock_success_sound
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] →
      statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : isolateBlock (coreBlock statement policy) input =
      .ok body next) :
    DeclarativeGrammar.IsolatedCoreBlockParses
      (DeclarativeGrammar.CoreBlockParses statementParses
        policy.declarative)
      input.declarativeRemainder body next.declarativeRemainder := by
  exact isolateBlock_success_sound
    (DeclarativeGrammar.CoreBlockParses statementParses policy.declarative)
    (coreBlock statement policy)
    (coreBlock_success_sound statementParses statement policy
      statementReflects statementSound)
    diagnosticFree result

/-- Isolated raw Core blocks also reflect diagnostic freedom to their input. -/
theorem isolatedCoreBlock_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (coreBlock statement policy)) :=
  isolateBlock_reflectsDiagnosticFreeOnSuccess (coreBlock statement policy)
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement policy
      statementReflects)

end Solcore.Syntax.Parser
