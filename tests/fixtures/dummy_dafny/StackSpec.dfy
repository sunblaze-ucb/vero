// Specifications and lemmas about the Stack datatype.

include "Stack.dfy"

lemma push_pop_roundtrip<T>(s: Stack<T>, v: T)
  ensures pop(push(s, v)) == s
{
}

lemma push_increases_size<T>(s: Stack<T>, v: T)
  ensures size(push(s, v)) == size(s) + 1
{
}

lemma size_toSeq<T>(s: Stack<T>)
  ensures size(s) == |toSeq(s)|
{
  match s
  case Empty =>
  case Cons(_, rest) =>
    size_toSeq(rest);
}

lemma push_toSeq<T>(s: Stack<T>, v: T)
  ensures toSeq(push(s, v)) == [v] + toSeq(s)
{
}

lemma peek_push<T>(s: Stack<T>, v: T)
  ensures peek(push(s, v)) == v
{
}

lemma isEmpty_push<T>(s: Stack<T>, v: T)
  ensures !isEmpty(push(s, v))
{
}

lemma isEmpty_empty<T>()
  ensures isEmpty(Empty)
{
}
