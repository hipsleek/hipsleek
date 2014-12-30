data node { int val ; node next }.


pred lseg<n, p> == self = p & n = 0
         or self::node<next = r> * r::lseg<n - 1, p>
         inv n >= 0.

lemma self::lseg<n, p> & n = a + b & a,b >=0 <-> self::lseg<a, r> * r::lseg<b, p>.

checkentail x::lseg<n, p> & n = 7 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 = 3 & n2 = 4.
//print residue.
// valid

//checkentail x::lseg<n1, r1> * r1::lseg<n2, p> & n1 = 3 & n2 = 4 |- x::lseg<n, p> & n = 7.
// should be valid but it fails due to the lemma folding which is not weel-done (it simply unfolds the consequent)
// todo: fix the lemma folding
//print residue.

//checkentail x::lseg<n, p> & n = 7 |- x::lseg<n1, r1> * r1::lseg<n2, p> & n1 = 4 & n2 = 3.
// valid
//print residue.

//checkentail x::lseg<n, p> & n = 6 |- (exists p1, p2: x::lseg<n1, r1> * r1::lseg<n2, p> & n1 = p1 & n2 = p2 & p1 = p2).
//checkentail x::lseg<n, p> & n = 6 |- x::lseg<n1, r1> * r1::lseg<n2, p> & n1 = p1 & n2 = p2 & p1 = p2.

//checkentail x::lseg<n, p> & n = 6 |- x::lseg<n1, r1> * r1::lseg<n2, p> & n1 = n2.
// valid 

//checkentail x::lseg<n, p> * t1::lseg<x1, y1> & n = 6 |- t1::lseg<x2, y2> * x::lseg<n1, r1> * r1::lseg<n2, p> & n1 = n2.
// valid

//checkentail x::lseg<n, p> & n = 7 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 = 3 & n2 = 4.
// valid
//print residue.

//checkentail x::lseg<n, p> & n = 7 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 >= 1 & n2 >= 2.
// valid
//print residue.

//checkentail x::lseg<n, p> & n > 10 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 >= 1 & n2 >= 2.
// valid

//checkentail x::lseg<n, p> & n > 10 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 >= 9 & n2 >= 2.
// valid
//checkentail x::lseg<n, p> & n > 9 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 >= 9 & n2 >= 2.
// fail
//checkentail x::lseg<n, p> & n > 10 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 >= 10 & n2 <= 2.
// valid

//checkentail x::lseg<n, p> & n > 10 |- x::lseg<n1, r1> * r1::lseg<n2, r2> * r2::lseg<n3, r3> & n1 <= 1 & n2 <= 2 & n3 >= 5.
// valid
//checkentail x::lseg<n, p> & n > 10 |- x::lseg<n1, r1> * r1::lseg<n2, r2> * r2::lseg<n3, r3> & n1 >= 1 & n2 >= 2 & n3 >= 5.
// valid

//checkentail x::lseg<n, p> & n > 10 |- x::lseg<n1, r1> * r1::lseg<n2, r2> * r2::lseg<n3, r3> & n1 >= 1 & n2 >= 2 & n3 >= 1.
// valid

//checkentail x::lseg<n, p> & n = 7 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 = 3 & n2 = 5.
// fail

//checkentail x::lseg<n, p> & n = 7 |- x::lseg<n1, r1> * r1::lseg<n2, r2> & n1 = 3 & n2 = 3.
// valid

//checkentail x::lseg<n, p> & n = 7 |- x::lseg<n1, r1> * r1::lseg<n2, p> & n1 = 3 & n2 = 3.
// fail
