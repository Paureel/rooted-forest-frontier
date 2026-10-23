import ProductTopology
-- Uncut incompatible gadget cannot be a compatible terminal component.
example : RMAF.restrictionAgrees (ProductTopology.sourceGadget 0)
    (ProductTopology.targetGadget 0) [1,2,3] = true := by decide
