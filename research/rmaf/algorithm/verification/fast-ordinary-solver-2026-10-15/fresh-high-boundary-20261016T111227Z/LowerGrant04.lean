-- Lower-fact grant audit; exact statements were isolated in LowerTypes03.
import NativeAuditCore
run_cmd StageAudit.audit #[`RestrictionBridge.restricted_labels_exact,
  `RestrictionBridge.restriction_exists, `RestrictionBridge.restrict_labels,
  `RestrictionBridge.root_not_prepend] "lower-grant-v1"
