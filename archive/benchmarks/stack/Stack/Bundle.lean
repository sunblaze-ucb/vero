import Stack.Impl.Stack
import Stack.Impl.BalancedParentheses
import Stack.Impl.InfixToPostfixConversion
import Stack.Impl.InfixToPrefixConversion
import Stack.Impl.DijkstrasTwoStackAlgorithm

/-!
# Stack.Bundle

Per-package implementation bundle for the `Stack` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure StackBundle where
  isEmpty                    : Stack.IsEmptySig
  size                       : Stack.SizeSig
  isFull                     : Stack.IsFullSig
  peek                       : Stack.PeekSig
  pop                        : Stack.PopSig
  contains                   : Stack.ContainsSig
  fromList                   : Stack.FromListSig
  balancedParentheses        : BalancedParenthesesSig
  infixToPostfix             : InfixToPostfixSig
  infix2Postfix              : Infix2PostfixSig
  infix2Prefix               : Infix2PrefixSig
  dijkstrasTwoStackAlgorithm : DijkstrasTwoStackAlgorithmSig
