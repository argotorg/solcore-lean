import Solcore.Syntax.Parser.SourceFrameProperties
import Solcore.Syntax.Parser.Delimited

/-! Every ordinary delimiter outcome retains its input file when its child
does. No token/window, progress, adequacy, or validity assumption is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem closeDelimited_preservesFile {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α) :
    Parser.PreservesFile (closeDelimited opening closing context elementsRev) := by
  intro input
  unfold closeDelimited
  cases result : symbol closing context input with
  | ok token next => exact (symbol_preservesFile closing context).file_eq_of_ok result
  | reject failure rejected => exact (symbol_preservesFile closing context).file_eq_of_reject result
  | invariant error => trivial

theorem afterDelimitedElement_preservesFile {α : Type}
    (element : Parser α) (childFile : Parser.PreservesFile element)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev,
      Parser.PreservesFile (afterDelimitedElement element closing allowTrailing context phase opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input; trivial
  | succ fuel ih =>
      intro elementsRev input
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context input with
        | invariant error => trivial
        | reject failure rejected => exact (symbol_preservesFile .comma context).file_eq_of_reject commaResult
        | ok comma afterComma =>
            have commaFile := (symbol_preservesFile .comma context).file_eq_of_ok commaResult
            simp only
            split
            · exact (closeDelimited_preservesFile opening closing context elementsRev afterComma).trans commaFile
            · cases elementResult : element afterComma with
              | invariant error => trivial
              | reject failure rejected => exact Eq.trans (childFile.file_eq_of_reject elementResult) commaFile
              | ok value next =>
                  simp only
                  split
                  · exact (ih (value :: elementsRev) next).trans
                      (Eq.trans (childFile.file_eq_of_ok elementResult) commaFile)
                  · trivial
      · split
        · exact closeDelimited_preservesFile opening closing context elementsRev input
        · exact rejectAt_preservesFile input _ context

theorem delimitedWithPolicy_preservesFile {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (childFile : Parser.PreservesFile element) :
    Parser.PreservesFile (delimitedWithPolicy opening closing allowEmpty allowTrailing element context phase) := by
  intro input
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => trivial
  | reject failure rejected => exact (symbol_preservesFile opening context).file_eq_of_reject openingResult
  | ok openingToken afterOpening =>
      have openingFile := (symbol_preservesFile opening context).file_eq_of_ok openingResult
      simp only
      split
      · exact (closeDelimited_preservesFile openingToken closing context [] afterOpening).trans openingFile
      · cases elementResult : element afterOpening with
        | invariant error => trivial
        | reject failure rejected => exact Eq.trans (childFile.file_eq_of_reject elementResult) openingFile
        | ok value next =>
            simp only
            split
            · exact (afterDelimitedElement_preservesFile element childFile closing allowTrailing context phase
                openingToken (afterOpening.remainingCount + 1) [value] next).trans
                (Eq.trans (childFile.file_eq_of_ok elementResult) openingFile)
            · trivial

theorem delimited_preservesFile {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (childFile : Parser.PreservesFile element) :
    Parser.PreservesFile (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_preservesFile opening closing allowEmpty true element context phase childFile

end Solcore.Syntax.Parser
