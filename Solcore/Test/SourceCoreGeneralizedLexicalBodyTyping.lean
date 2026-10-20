import Solcore.Test.SourceCoreGeneralizedLexicalBodyFixture
import Solcore.Test.SourceCoreMixedImperativeTyping

/-! The complete lexical-body regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreGeneralizedLexicalBody
