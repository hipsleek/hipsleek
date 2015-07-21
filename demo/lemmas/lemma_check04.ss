//Valid.Fail.Fail
data node { int val ; node next }

ll<n> == self = null & n = 0
	or self::node<next = r> * r::ll<n - 1>
  inv n >= 0;

sortl<n, mi> == self::node<mi,null> & n=1
	or self::node<mi, r> * r::sortl<n - 1, k> & mi <= k
  inv n >= 1 & self!=null;

lemma "L41" self::sortl<n, mi> -> self::ll<n>;

lemma "L42" self::sortl<n, mi> & n = 3 -> self::ll<m> & m=4;

lemma "L43" self::sortl<n, mi> <- self::ll<n>;


