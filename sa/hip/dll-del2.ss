data node2 {
	int val;
	node2 prev;
	node2 next;
}

dll<p> == self = null 
  or self::node2<_ ,p , q> * q::dll<self> // = q1
	inv true;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

void delete(node2 x)
  /* infer[n] */

/*
  requires x::node2<_,p,q>*q::dll<x> & q!=null
  ensures x::node2<_,p,r>*r::dll<x> ;

  infer[H1,G1]
  requires H1(x)
  ensures  H1(x);
*/


  requires dll<p>
  ensures  dll<q>;

{
  bool l = x.next.next==null;
  if (l) {
    // dprint;
    x.next = null;
    }
  else
    delete(x.next);
}


/*


[ H1(x_683) ::= x_683::node2<val_26_568,prev_26_569,next_29_544'>@M 
  * HP_684(prev_26_569,next_29_544')&true,

 HP_684(prev_26_569,next_29_544') ::= 
   next_29_544'::node2<val_26_537',prev_26_678,next_26_677>@M * 
   prev_26_569::node2<val_26_568,prev_26_685,next_29_686>@M * 
   HP_684(prev_26_685,next_29_686) * 
   next_26_677::node2<val_26_537',prev_26_679,next_26_680>@M * 
   HP_570(prev_26_679) * 
   next_26_680::node2<val_26_568,prev_26_685,next_29_686>@M * 
   HP_684(prev_26_685,next_29_686) * 
   prev_26_678::node2<val_26_568,prev_26_685,next_29_686>@M * 
   HP_684(prev_26_685,next_29_686)&true
 or prev_26_569::node2<val_26_568,prev_26_689,next_29_690>@M *  (1 node)
    HP_684(prev_26_689,next_29_690)&next_29_544'=null
 or next_29_544'::node2<val_26_537',prev_26_678,next_26_677>@M * 
    prev_26_569::node2<val_26_568,prev_26_693,next_29_694>@M * 
    HP_684(prev_26_693,next_29_694) * 
    prev_26_678::node2<val_26_568,prev_26_693,next_29_694>@M * 
    HP_684(prev_26_693,next_29_694)&next_26_677=null
 or next_29_544'::node2<val_26_537',prev_26_678,next_26_677>@M * 
    prev_26_569::node2<val_26_568,prev_26_697,next_29_698>@M * 
    HP_684(prev_26_697,next_29_698) * 
    next_26_677::node2<val_26_537',prev_26_681,next_26_682>@M * 
    next_26_682::node2<val_26_568,prev_26_697,next_29_698>@M * 
    HP_684(prev_26_697,next_29_698) * 
    prev_26_678::node2<val_26_568,prev_26_697,next_29_698>@M * 
    HP_684(prev_26_697,next_29_698)&true
 or next_29_544'::node2<val_26_568,prev_26_701,next_29_702>@M * 
    HP_684(prev_26_701,next_29_702) * 
    prev_26_569::node2<val_26_568,prev_26_701,next_29_702>@M * 
    HP_684(prev_26_701,next_29_702)&true
 ,
 HP_570(prev_26_708) ::= HP_559(prev_26_708)&true,
 HP_559(prev_26_707) ::= HP_559(prev_26_707)&true]






[ G1(x_637) ::= x_637::node2<val_26_568,prev_26_569,next_28_544'>@M * HP_638(prev_26_569,next_28_544')&true,
 H1(x_643) ::= 
    x_643::node2<val_26_533',prev_26_534',next_26_535'>@M *HP_559(prev_26_534') *
         next_26_535'::node2<val_26_537',prev_26_634,next_26_633>@M *  HP_570(prev_26_634)&next_26_633=null
 or x_643::node2<val_26_533',prev_26_534',next_26_535'>@M * HP_559(prev_26_534') *
         next_26_535'::node2<val_26_537',prev_26_634,next_26_633>@M * HP_570(prev_26_634)&next_26_633!=null
 or next_26_535'::node2<val_26_537',prev_26_634,next_26_633>@M * HP_570(prev_26_634) *
          x_643::node2<val_26_533',prev_26_534',next_26_535'>@M * HP_559(prev_26_534')&true
 or HP_638(prev_26_569,next_28_544')&true
 ,
 HP_638(prev_26_569,next_28_544') ::= 
 HP_559(prev_26_569) * next_28_544'::node2<val_26_568,prev_26_639,next_28_640>@M * HP_638(prev_26_639,next_28_640)&true
 or HP_559(prev_26_569)&next_28_544'=null
 ]
*************************************



*/
