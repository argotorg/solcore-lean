import Solcore.Syntax.DeclarativeYulStatementTerminatedBoundaryProperties

/-!
Parser-independent level bundle for recursive inline-Yul statements.

One level packages clean success, broader ordinary success, exact rejection,
and the laws needed to use that level inside the next recursive block.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete declarative approximation of recursive Yul statements. -/
structure YulStatementLevel where
  cleanParses : Remainder → Syntax.YulStmt → Remainder → Prop
  ordinaryParses : Remainder → Syntax.YulStmt → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects
  cleanToOrdinary : ∀ {input statement output},
    cleanParses input statement output →
      ordinaryParses input statement output

namespace YulStatementLevel

/-- Fuel zero recognizes no statement success or rejection outcome. -/
def empty : YulStatementLevel where
  cleanParses := fun _ _ _ => False
  ordinaryParses := fun _ _ _ => False
  rejects := fun _ _ => False
  outcomes := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed
      exact False.elim leftParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact False.elim rejection
  }
  cleanToOrdinary := by
    intro input statement output parsed
    exact False.elim parsed

/-- Compose one core outcome with maximal optional termination and the outer
recovering statement layer. -/
def ofCore
    (cleanCore ordinaryCore :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (coreRejects : Remainder → Remainder → Prop)
    (coreOutcomes : DeterministicOutcomeSpec ordinaryCore coreRejects)
    (cleanCoreToOrdinary : ∀ {input statement output},
      cleanCore input statement output →
        ordinaryCore input statement output)
    (coreBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output, ordinaryCore input statement output) :
    YulStatementLevel where
  cleanParses := YulStatementTerminatedParses cleanCore
  ordinaryParses := YulStatementLayerOrdinaryParses
    (YulStatementTerminatedOrdinaryParses ordinaryCore)
    (YulStatementTerminatedRejects coreRejects)
  rejects := YulStatementRejects
  outcomes := yulStatementLayerDeterministicOutcomeSpec
    (yulStatementTerminatedDeterministicOutcomeSpec coreOutcomes)
    (YulStatementRejects.disjointTerminatedOrdinary coreBoundaryDisjoint)
  cleanToOrdinary := by
    intro input statement output parsed
    exact .terminated (parsed.toOrdinary cleanCoreToOrdinary)

end YulStatementLevel

end Solcore.Syntax.DeclarativeGrammar
