// A simple generic stack implementation for pipeline testing.

datatype Stack<T> = Empty | Cons(top: T, rest: Stack<T>)

// Core stack operations — these are the API (implementations)
function method push<T>(s: Stack<T>, v: T): Stack<T>
{
  Cons(v, s)
}

function method pop<T>(s: Stack<T>): Stack<T>
  requires s.Cons?
{
  s.rest
}

function method peek<T>(s: Stack<T>): T
  requires s.Cons?
{
  s.top
}

function method size<T>(s: Stack<T>): nat
{
  match s
  case Empty => 0
  case Cons(_, rest) => 1 + size(rest)
}

// Spec helpers — these describe behavior for specifications
function toSeq<T>(s: Stack<T>): seq<T>
{
  match s
  case Empty => []
  case Cons(top, rest) => [top] + toSeq(rest)
}

predicate isEmpty<T>(s: Stack<T>)
{
  s.Empty?
}

method Main()
{
  var s := Empty;
  s := push(s, 1);
  s := push(s, 2);
  assert peek(s) == 2;
  assert size(s) == 2;
  s := pop(s);
  assert peek(s) == 1;
  assert size(s) == 1;
}
