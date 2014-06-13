data node {
  int val;
  node next;
}

blseg<y,lb,ub> ==            // ~~ in GRASShopper: blseg<x,y,lb,ub>
     self = y & lb<=ub
  or self::node<val,next> * next::blseg<y,lb,ub>
   & self != y 
       & lb <= val & val <= ub
 inv lb<=ub;

bslseg<y,lb,ub> ==           // ~~ in GRASShopper: blseg<x,y,lb,ub>
     self = y & lb<=ub
  or self::node<val,next> * next::bslseg<y,val,ub>
       & self != y 
       & lb <= val & val <= ub
 inv lb<=ub;

lemma_unsafe self::bslseg<y,lx,up> 
  <- self::bslseg<p,lx,ux> * p::bslseg<y,lp,up> & ux<=lp; 

/*
lemma_safe self::bslseg<y,lx,up> * y::node<a,b>
  <- self::bslseg<p,lx,ux> * p::bslseg<y,lp,up>  
     * y::node<a,b> & ux<=lp

lemma_safe self::bslseg<null,lx,up> 
  <- self::bslseg<p,lx,ux> * p::bslseg<null,lp,up>  
     & ux<=lp
*/

node quicksort(node x, node y, int lb, int ub)
 case {
   y=null -> 
     requires x::blseg<y,lb,ub>
     ensures res::bslseg<y,lb,ub>;
   y!=null ->
    requires x::blseg<y,lb,ub> * y::node<a,b>
    ensures res::bslseg<y,lb,ub> * y::node<a,b>;
 }
{
  node rx;
  node pivot;
  node z;
  if ((x != y)) {
    /*
     * condition in GRASShopper: if ((x != y) && (x.next != y)) {...}
     * --> change to HIP:    if (x != y) {
     *                         assume x::node<_,_>
     *                         if (x.next != y)
     */
    //assume x::node<_,_>;
    //assert false;
    //dprint;
    if (x.next != y) {
      split1(x,y,lb,ub,rx,pivot);
      //dprint;
      assert pivot'!=null;
      //int v = pivot.val;
      rx = quicksort(rx,pivot,lb,pivot.val);
      z = quicksort(pivot.next,y,pivot.val,ub);
      pivot.next = z;
    }
    else {
      rx = x;
    }
  }
  else {
    rx = x;
  }
  return rx;
}

void split1(node x, node y, int lb, int ub, ref node rx, ref node pivot)
  requires x::blseg<y,lb,ub> & (x != y)
  ensures rx'::blseg<pivot',lb,pv> 
            * pivot'::node<pv,pn>
            * pn::blseg<y,pv,ub>
            & pivot' != y 
            & lb <= pv & pv <= ub;
