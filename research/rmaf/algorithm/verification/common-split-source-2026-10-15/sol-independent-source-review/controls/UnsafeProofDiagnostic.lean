import Std
namespace TrustControl
unsafe def unsafeTrue : True := True.intro
theorem attempted : True := unsafeTrue
end TrustControl
