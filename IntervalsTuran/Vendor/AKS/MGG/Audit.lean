/-
Kernel dependency audit for the imported MGG theorem and local adapter.
The diagnostic commands remain outside any exported section. The module
header lets the project-wide root import this verification companion.
-/
module

import IntervalsTuran.Vendor.AKS.MGG.Adapter

#print axioms spectralGap_mgg
#print axioms spectralGap_iterSquare
#print axioms IntervalsTuran.Spectral.MGG.mgg_hasPermutationPorts
#print axioms IntervalsTuran.Spectral.MGG.graph_gap_le
#print axioms IntervalsTuran.Spectral.MGG.portPerm
#print axioms IntervalsTuran.Spectral.MGG.sum_square_le

