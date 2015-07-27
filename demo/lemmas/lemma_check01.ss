//Valid.Valid.Fail
data node { int val ; node next }

lseg<n, p> == case {
     n=0 -> [] self = p & n = 0;
     n!=0 ->  [] self::node<next = r> * r::lseg<b,p> & b=n-1; 
     }
inv n >= 0.

lemma "V1" self::lseg<n, p> & n = a + b & a,b >=0 -> self::lseg<a, r> * r::lseg<b, p>;
// Valid 

// Valid 

lemma "V2" self::lseg<n, p> & n = a + b & a,b >=0 <- self::lseg<a, r> * r::lseg<b, p>;
// Valid

lemma "F3" self::lseg<n, p> -> (exists a,b,r: self::lseg<a, r> * r::lseg<b, p> & n=a+b+2);
// Fail

