//Valid.Valid.Fail.
data node { int val ; node next }

ll<n> == self = null & n = 0
	or self::node<next = r> * r::ll<n - 1>
  inv n >= 0;

lemma "L1" self::ll<n> & n > 0 -> self::ll<m> & m > 0;

lemma "L2" self::ll<n> & n >0 <- self::ll<n> & n = 2;

lemma "L4" self::ll<n> & n >0 -> self::ll<n> & n = 2;

