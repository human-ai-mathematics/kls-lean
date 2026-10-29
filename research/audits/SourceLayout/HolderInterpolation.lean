import Lean
import FunctionalInequalities.Analysis.Holder.Cutoff

/-! The old interpolation telescope retains alpha <= 1, including zero distance and negative alpha. -/

universe u u_1 u_2 u_3

example :
∀ {t D α : ℝ},
  LE.le.{0} 0 t →
    LE.le.{0} t D →
      LE.le.{0} α 1 →
        LE.le.{0} t (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} D (HSub.hSub.{0, 0, 0} 1 α)) (HPow.hPow.{0, 0, 0} t α)) :=
  @FunctionalInequalities.Analysis.le_rpow_one_sub_mul_rpow

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.Analysis.Newtonian." ||
        name.toString.startsWith "FunctionalInequalities.KLS." then
      throwError "Holder cutoff tools must remain below Newtonian and KLS"
