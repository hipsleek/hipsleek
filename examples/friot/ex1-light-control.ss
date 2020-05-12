hip_include 'node.ss'
hip_include 'hodef.ss'
hip_include 'commprimitives.ss'


global int WAIT;
global int READY;
global int LIGHTUP;
global int TICK;
global Channel c;

void events()
  requires true
  ensures c::Chan{@S emp}<>
         & WAIT!=READY
         & WAIT!=LIGHTUP
         & WAIT!=TICK
         & READY!=LIGHTUP
         & READY!=TICK
         & LIGHTUP!=TICK;

void until_ready ()
     requires true
     ensures  c::Chan{@S ?v#v=READY ;; ?v#v=READY }<>; // ("Wait"∗ · "Ready") V ("Wait"ω );
{
 events();
 ev(c,READY);
 ev(c,READY);
 dprint;
 // if (temp>20)  ev(c,READY);
 // else {ev(c,WAIT); until_ready ();}
}

pred_prim EVENT<ev,card>;

lemma_norm self::Chan{@S ?v#v=READY ;; EVENT<READY,x>}<> & y= x+1 ->
           self::Chan{@S EVENT<READY,y> }<>;

void foo (int t)
     requires c::Chan{@S %R }<> & READY \in %R
     ensures  c::Chan{@S %R ;; EVENT<READY,t> }<>;
{
 events();
 if (t!=0) {
   ev(c,READY);
    dprint;
    foo(t-1);
    dprint;
 }
 dprint;
}
