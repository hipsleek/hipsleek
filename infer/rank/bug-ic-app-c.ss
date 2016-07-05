data node {
	int val;
	node next;
}


ll3<n,s,l> == self=null & n=0 & s<=l
    or self::node<s, q> * q::ll3<n-1,s1,l> & s<=s1
	inv n>=0 & s<=l;

ranking rk(int a, int b).
relation A(int a, int b, int c).
relation P(int a, int b, int c, int d).

/*
This example wrongly inferred pre with [l1,l2,s1,s2]

  Inferred Pure :[s1<=s2, s1<=l1]

which seems unsound. I did a trace below:

quan_var: :[n,q_615,y,m,q_579,l_577,flted_8_578,s1_580,s_576,s1_616]
@4! iv: :[l1,s2,s1,l2]
@4! new_p1: : l1<s1 | s1<=l1 & s1<=s2 | l2<s2 & s2<s1 & s1<=l1
@4! new_p2: : s1<=l1 & s1<=s2
@4! new_p2 (pairwisecheck): : s1<=l1 & s1<=s2

new_p1 seems OK. A key thing to use is the invariant at the pre-state
of the form:

# B:={[s1,s2,l1,l2]:s1<=l1 & s2<=l2};

If this is conjoined with new_p1, we would obtain:

# A:={[s1,s2,l1,l2]: l1<s1 | s1<=l1 & s1<=s2 | l2<s2 & s2<s1 & s1<=l1};
# B:={[s1,s2,l1,l2]:s1<=l1 & s2<=l2};
# A intersection B;

{[s1,s2,l1,l2]: s1 <= s2 <= l2 && s1 <= l1}

After removing the invariant (using gist), we would have
the correct outcome, namely:

{[s1,s2,l1,l2]: s1 <= l2 }


@4! rhs_xpure: : s_576<=s1_616


*/

void append3(node x, node y)
  //infer [l1,s2]
  infer [P]
  requires x::ll3<n,s1,l1>*y::ll3<m,s2,l2>  & x!=null
  ensures x::ll3<n+m,s1,l2>  & P(l1,s2,l2,s1) ;
{
   if (x.next==null) {
     //assume false;
     x.next=y;
   } else {
      append3(x.next,y);
   }
}


