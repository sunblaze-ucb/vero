import Netaddr.Impl.Cidr

/-!
# Netaddr.Bundle

Per-package implementation bundle for the `Netaddr` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure NetaddrBundle where
  containsAddr   : Netaddr.ContainsAddrSig
  networkAddr    : Netaddr.NetworkAddrSig
  broadcast      : Netaddr.BroadcastSig
  spanningCidr   : Netaddr.SpanningCidrSig
  iprangeToCidrs : Netaddr.IprangeToCidrsSig
