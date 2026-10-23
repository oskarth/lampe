import Lampe
open Lampe Lampe.Crypto Lampe.Crypto.EmbeddedCurve
namespace Checks.Bn254

theorem bn254_generator_nonsingular :
    (affineCurve Bn254.prime).Nonsingular 1
      (17631683881184975370165255887551781615748388533673675138860 : Fp Bn254.prime) := by
  decide


#print axioms bn254_generator_nonsingular

end Checks.Bn254
