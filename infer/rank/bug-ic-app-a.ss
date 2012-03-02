data node {
	int val;
	node next;
}


ll3<n,s,l> == self=null & n=0 & s<=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

relation pp(int a, int b).

// an Omega bug when we use "memo_rel_hole"
// which got truncated to "mo_rel_hole"
void append3(node x, node y)
  infer [pp]
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null & pp(l1,s2) 
//& Term[n]
  ensures x::ll3<n+m,s1,l2> ;
{
   if (x.next==null) {
     x.next=y;
   } else {
     //assume false;
      append3(x.next,y);
   }
}


