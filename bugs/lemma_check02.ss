//Fail.Valid.
data node { int val ; node next }

lseg<n, p> == case {
     n=0 -> [] self = p & n = 0;
     n!=0 ->  [] self::node<next = r> * r::lseg<b,p> & b=n-1; 
     }
inv n >= 0;
/*
lseg<n, p> == self = p & n = 0
         or self::node<next = r> * r::lseg<n - 1, p>
  inv n >= 0;
*/

lemma "F5" self::lseg<n, p> <- (exists a,b,r: self::lseg<a, r> * r::lseg<b, p> & n=a+b+2);

/*lemma "V6" self::lseg<n, p> <-> (exists a,b: self::lseg<a, r> * r::lseg<b, p> & n=a+b);*/
