import Ipaddress.Impl.Cidr

/-!
# Ipaddress.Bundle

Per-package implementation bundle for the `Ipaddress` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure IpaddressBundle where
  containsAddr : Ipaddress.ContainsAddrSig
  networkAddr  : Ipaddress.NetworkAddrSig
  broadcast    : Ipaddress.BroadcastSig
  supernet     : Ipaddress.SupernetSig
  collapse     : Ipaddress.CollapseSig
