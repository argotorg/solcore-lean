import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyProfile

/-! Bounded instances retain the original lambda and its finite lexical body.
The common scanner carries each original expression and declaration receipt;
no body execution law is part of the profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
abbrev Profile := GeneralizedLocalOrdinaryBodyProfile.Profile
abbrev profile? := GeneralizedLocalOrdinaryBodyProfile.profile?
end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
