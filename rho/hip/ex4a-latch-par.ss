/*
  Example with simple CountDownLatch
 */

//CountDownLatch
data CDL{
}

data cell{
  int val;
}

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;

pred_prim CNT<n:int>
inv n>=(-1);

lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>;

//lemma "zero" self::CNT<a> -> self::CNT<a> * self::CNT<b> & b = 0;

/********************************************/
CDL create_latch(int n) with %P
  requires n>0
  ensures res::LatchIn{-%P}<> * res::LatchOut{+%P}<> * res::CNT<n>;
  requires n=0
  ensures res::CNT<(-1)>;

void countDown(CDL c)
  requires c::LatchIn{-%P}<> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  requires c::CNT<(-1)> 
  ensures c::CNT<(-1)>;

void await(CDL c)
  requires c::LatchOut{+%P}<> * c::CNT<0>
  ensures c::CNT<(-1)> * %P;
  requires c::CNT<(-1)>
  ensures c::CNT<(-1)> * %P;
  
void main()
  requires emp ensures emp;
{
  cell x, y;
  CDL c = create_latch(1) with x'::cell<1> * y'::cell<2> * @full[x, y];
  int r1,r2;
  r1=0; r2=0;
  //dprint;
  par {x, y, r1, r2, c@L}
  {  
   // exists r1',r2'
   case {x,y,c@L} c'::LatchIn{- x'::cell<1> * y'::cell<2> * @full[x, y]}<> * c'::CNT<(1)> -> 
        //dprint;
        x = new cell(1); 
        //dprint;
        y = new cell(2); 
      dprint;
      countDown(c);
      //dprint;
      //int k = x.val;
  || 
    // exists x',y',r2'
    case {r1,c@L} c'::LatchOut{+x'::cell<1> * @full[x]}<> * c'::CNT<0> -> // TODO: Should return error here
      //dprint;
      await(c); 
      r1 = x.val; 
  || 
     // exists r1',x',y'
     case {r2,c@L} c'::LatchOut{+y'::cell<2> * @full[y]}<> * c'::CNT<0> ->
       //dprint;
       await(c); r2 = y.val;
  }
  dprint;
}

/*
# ex4a.ss

      x = new cell(1); 
      y = new cell(2); 
      dprint;
      countDown(c);
      dprint;
      int k = x.val;

How come no printing?
How come can still access x.val?

What is:
       EXISTS(v_int_47_1431': c_42'::LatchIn<> * c_42'::LatchOut<> * c_42'::CNT<v_int_47_1431'>&v_int_47_1431'=1)[]


Successful States:
[
 Label: []
 State:(exists v_int_47_1431': c_42'::LatchIn{ - (exists flted_47_1581,flted_47_1582: x_40'::cell<flted_47_1582> * 
y_41'::cell<flted_47_1581>&flted_47_1582=1 & flted_47_1581=2&
{FLOW,(4,5)=__norm#E})[]}<> * c_42'::LatchOut{ + (exists flted_47_1583,flted_47_1584: x_40'::cell<flted_47_1584> * 
y_41'::cell<flted_47_1583>&flted_47_1584=1 & flted_47_1583=2&
{FLOW,(4,5)=__norm#E})[]}<> * c_42'::CNT{}<v_int_47_1431'>&v_int_47_1431'=1&{FLOW,(4,5)=__norm#E})[]
       EXISTS(v_int_47_1431': c_42'::LatchIn<> * c_42'::LatchOut<> * c_42'::CNT<v_int_47_1431'>&v_int_47_1431'=1)[]

 ]


*/
