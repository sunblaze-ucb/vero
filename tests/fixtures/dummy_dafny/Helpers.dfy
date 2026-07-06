// Utility types and functions built on top of Stack.

include "Stack.dfy"

type Element = int

// Trivial constructor helper
function method defaultStack(): Stack<Element>
{
  Empty
}

// API operations that build on core stack ops
function method fromSeq<T>(xs: seq<T>): Stack<T>
{
  if |xs| == 0 then Empty
  else push(fromSeq(xs[1..]), xs[0])
}

function method reverse<T>(s: Stack<T>): Stack<T>
{
  fromSeq(toSeq(s))
}
