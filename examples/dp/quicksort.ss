data node {
  int val;
  node next;
}

blseg<y,lb,ub> ==            // ~~ in GRASShopper: blseg<x,y,lb,ub>
     self = y
  or self::node<val,next> * next::blseg<y,lb,ub>
       & self != y & lb <= val & val <= ub;

bslseg<y,lb,ub> ==           // ~~ in GRASShopper: blseg<x,y,lb,ub>
     self = y
  or self::node<val,next> * next::bslseg<y,lb,ub>
       & self != y & lb <= val & val <= ub;

node quicksort(node x, node y, int lb, int ub)
  requires x::blseg<y,lb,ub>
  ensures res::bslseg<y,lb,ub>;
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
    assume x::node<_,_>;
    if (x.next != y) {
      split1(x,y,lb,ub,rx,pivot);
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
  ensures rx::blseg<pivot,lb,pivot.val> * pivot::blseg<y,pivot.val,ub>
            & pivot != y & lb <= pivot.val & pivot.val <= ub;