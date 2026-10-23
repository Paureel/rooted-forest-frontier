import AuditSupport
import ToyExchangeRestriction
namespace ToyRoute
structure Packet where
  value : Nat
private def hiddenId (r : ToyExchangeRestriction.ExchangeRestriction) : ToyExchangeRestriction.ExchangeRestriction := r
def identity (r : ToyExchangeRestriction.ExchangeRestriction) : ToyExchangeRestriction.ExchangeRestriction := r
def projected (r : ToyExchangeRestriction.ExchangeRestriction) : Nat := r.value + 1
theorem harmless : True := True.intro
end ToyRoute
