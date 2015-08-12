data node {
 int val;
 node next;
}

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;
  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;

  gg<p> == self=null or self=p or self::node<_,q>*q::gg<p>;

  ll2<q> == self=null or self::node<_,q>;
  ll_not_one<pp> == self=null or self::node<v,pp> & v!=1;
  ll_not_one2<> == self=null or self::node<v,pp>*pp::ll<> & v!=1;

  ll_one<> == self=null or self::node<1,q>*q::ll_one<>;


bool check_ones(node x)
/* fails precond
  requires x::lseg<p>@L*p::ll2<q>@L
  ensures true;
*/
/* verifies
  requires x::lseg<p>@L*p::ll<>@L
  ensures true;
  requires x::lseg_one<p>@L*p::ll_not_one<q>@L
  ensures true;
  requires x::lseg_one<p>*p::ll_not_one<q>
  ensures true;
  requires x::lseg_one<p>@L*p::ll_not_one<q>@L
  ensures res & p=null | !res & p!=null;
  requires x::lseg<p>*p::ll<>
  ensures true;
  requires x::ll_one<>@L
  ensures res;
  requires x::lseg_one<p>@L*p::node<v,_>@L & v!=1
  ensures !resxs;
  requires x::lseg_one<p>@L*p::node<v,_>@L & v!=1
  ensures !res;
  requires x::lseg<p>*p::ll<>
  ensures x::lseg<p>*p::ll<>;
  requires x::ll<>
  ensures x::ll<>;
  requires x::ll<>
  ensures x::lseg<p>*p::ll<>;
  requires x::ll<>
  ensures x::lseg_one<p>*p::ll_not_one2<>;
  requires x::ll<>
  ensures x::lseg_one<p>*p::ll_not_one2<> & (res & p=null | !res & p!=null);
*/


  requires x::lseg_one<p>@L*p::ll_not_one2<>@L
  ensures res & p=null | !res & p!=null;

  requires x::lseg_one<p>@L*p::ll_not_one<q>@L*q::ll<>@A
  ensures res & p=null | !res & p!=null;

{ 
  if (x==null) return true;
  else {
   int t = x.val;
   if (t==1) return check_ones(x.next);
   else {
      //dprint;
       return false;
   }
 }
} 

/*
# ex4b.ss

The best shape-only spec we can try derive is:

  requires x::ll<>
  ensures x::lseg<p>*p::ll<>;

If we strengthen the post with content, we can proceed
to derive:

  requires x::ll<>
  ensures x::lseg_one<p>*p::ll_not_one2<> 
          & (res & p=null | !res & p!=null);

With immutability, we can change the pre-spec 
with the heap information from post-spec:

  requires x::lseg_one<p>@L*p::ll_not_one<q>*q::ll<>@L
  ensures res & p=null | !res & p!=null;

and later weaken slightly to:
  requires x::lseg_one<p>@L*p::ll_not_one<q>@L
  ensures res & p=null | !res & p!=null;

Note that the new pre is not stronger, as we have
the following provable lemma:
   x::ll<> <-> x::lseg_one<p>*p::ll_not_one<q>*q::ll<>
With this lemma, the final pre-condition is 
actually weaker than the original x::ll<>.
It had been made weaker by dropping the unaccessed
q::ll<> portion.

*/
