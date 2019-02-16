func int tf(node x) == ?.

data node {
	int val;
}

void sum(node x, node y)
requires x::node<a> * y::node<b>
ensures x::node<b> * y::node<a>;
{
   int m = x.val;
   int n = tf(y);
   x.val = n;
   y.val = m;
}

// example reasoning
// x::node<a> * y::node<b>
// int t = x.val;
// x::node<a> * y::node<b> & t = a
// x.val = y.val;
// x::node<b> * y::node<b> & t = a
// y.val = t;
// x::node<b> * y::node<t> & t = a
// |-
// x::node<b> * y::node<a>

// -----------------------------
// x::node<a> * y::node<b>
// int t = x.val;
// x::node<a> * y::node<b> & t = a
// // type inference: x.val; y.val; t
// x.val = ??;
// x::node<??> * y::node<b> & t = a
// y.val = t;
// x::node<??> * y::node<t> & t = a
// |-
// x::node<b> * y::node<a>
// <->
// x::node<??> t = a
// |-
// x'::node<b>

// -------------------------
// Motivating example: sorting using linked lists
// One or more error locations?