data node {
 int val;
 node next;
}

  ll3<> == self=null 
          or self::node<1,q>*q::ll3<>
          or self::node<v,q>*q::ll3<> & v!=1;

  ll<> == self=null 
    or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;
  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;

/*
  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;

*/

  gg<p> == self=null or self=p or self::node<_,q>*q::gg<p>;

//  ll2<q> == self=null or self::node<_,q>;
  ll_not_one<pp> == self=null or self::node<v,pp> & v!=1;
  ll_not_one2<> == self=null or self::node<v,pp>*pp::ll3<> & v!=1;

lemma_safe self::ll<> <-> self::lseg<p>*p::ll<>.

lemma_safe self::ll3<> <-> self::lseg_one<p>*p::ll_not_one2<>.


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

  requires x::lseg_one<p>@L*p::ll_not_one<q>@L
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
  ensures x::lseg_one<p>*p::ll_not_one2<> & (res & p=null | !res & p!=null);

With immutability, we can strengthen the pre-spec 
with the heap information from post-spec:

  requires x::lseg_one<p>@L*p::ll_not_one2<>@L
  ensures res & p=null | !res & p!=null;

and later weaken slightly to:
  requires x::lseg_one<p>@L*p::ll_not_one<q>@L
  ensures res & p=null | !res & p!=null;

Though it makes the pre stronger, it also helps
to make the post stronger through immutability
of its heap state.

Lastly, we may also have the lemma:
   x::ll<> <-> x::lseg_one<p>*p::ll_not_one<q>*q::ll<>
With this lemma, the current pre-condition is 
actually weaker than the original x::ll<>.

It was made weaker by dropping the unaccessed
q::ll<> portion.

*/
