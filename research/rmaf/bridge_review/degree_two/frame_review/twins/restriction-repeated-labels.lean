import Controls
open RMAF RestrictionRouteControls
example : ¬ ((leaves (.node (.leaf 0) (.leaf 0))).Nodup) := by decide
