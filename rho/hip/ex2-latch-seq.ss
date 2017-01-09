/*
  Example with simple CountDownLatch
 */

//CountDownLatch
data CDL{
}

data cell{
  int v;
}

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;

pred_prim CNT<n:int>
inv n>=(-1);

//lemma_split "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>;

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
  cell x = new cell(10);
  //assume x::cell<_>;
  CDL c = create_latch(1) with x'::cell<_>;
  //cell x = new cell(10);
  dprint;
  countDown(c);
  dprint;
  await(c);
  dprint;
}

/*
# ex1-latch-simple.ss

[
 Label: []
 State:
(exists flted_39_1602: c_42'::CNT{}<flted_39_1602> * x_41'::cell<Anon_11>
&exists(flted_38_51:0<=(flted_38_51+1)) & flted_39_1602+1=0 
& 0<=(flted_33_1599+1) & v_int_46_1576=10 & v_int_48_1587=1 
& n=v_int_48_1587 & Anon_11=v_int_46_1576 
& x_41'!=null & 0<=(v_int_48_1587+1) & flted_33_1599+1=n 
& 0<=(n+1)&{FLOW,(4,5
)=__norm#E})[]
       es_ho_vars_map: [Px_41'::cell<Anon_11>&{FLOW,(4,5)=__norm#E}[]; 
                        Px_41'::cell<Anon_11>&{FLOW,(4,5)=__norm#E}[]]

# print (P,x'_41...)
# what is below? why is it a repeat of above?
 
EXISTS(flted_39_1602: c_42'::CNT<flted_39_1602> * x_41'::cell<Anon_11>
&exists(flted_38_51:0<=(flted_38_51+1)) & flted_39_1602+1=0 
& 0<=(flted_33_1599+1) & v_int_46_1576=10 & v_int_48_1587=1 
& n=v_int_48_1587 & Anon_11=v_int_46_1576 
& x_41'!=null & 0<=(v_int_48_1587+1) & flted_33_1599+1=n 
& 0<=(n+1))[]

 */
