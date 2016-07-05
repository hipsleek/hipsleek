/* Example with simple CountDownLatch */

//CountDownLatch
data CDL {}

data cell { int val; }

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;

pred_prim CNT<n:int>
  inv n>=(-1);

lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

// Normalization lemma
lemma_prop "idemp-CNT" self::CNT<a> * self::CNT<(-1)> -> self::CNT<(-1)>;

lemma_prop "combine-CNT" self::CNT<a> * self::CNT<b> & a,b>=0 ->  self::CNT<a+b>;

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
  ensures c::CNT<(-1)>;

/********************************************/
void main()
  requires emp ensures emp;
{
  cell h;
  int v;
  CDL c = create_latch(1) with h'::cell<_>;
  par {h, v, c@L}
  {
    case {h, c@L} c'::LatchIn{- h'::cell<_>}<> * c'::CNT<(1)> ->
      h = new cell(1);
      countDown(c);
      //dprint;
    ||
    case {v, c@L} c'::LatchOut{+ h'::cell<_>}<> * c'::CNT<0> ->
      dprint;
      await(c);
      dprint;
      // how did we access "h" with zero permission?
      v = h.val + 1;
      //dprint;
  }
  dprint;

}

/*

Successful States:
[
 Label: []
 State:(exists flted_55_1820,Anon_1821,v_int_47_1822,Anon_1823,b_1824,b_1825,Anon_1827,h_40',Anon_13,v_int_47_1665: c_42'::LatchOut{ + h_40'::cell<Anon_13>&{FLOW,(4,5)=__norm#E}[]}<> * c_42'::CNT{}<flted_55_1820>*U@full[v_41]@lend[c_42]&0<v_int_47_1665 & v_int_47_1665=1 & v_int_47_1822=b_1824+1 & 0<=1 & 0<=b_1824 & Anon_1827=Anon_1821 & v_int_47_1822=1 & 0<v_int_47_1822 & Anon_1823=Anon_1827 & 0<=b_1825 & 0<=0 & b_1824=b_1825+0 & flted_55_1820=0&{FLOW,(4,5)=__norm#E}[]

 ]

dprint: ex11a-cdl.ss:58: ctx:  List of Failesc Context: [FEC(0, 0, 1  [])]

Successful States:
[
 Label: []
 State:(exists flted_37_1850: h_40'::cell<Anon_13> * c_42'::CNT{}<flted_18_1854>*N@full[v_41]@lend[c_42]&flted_18_1854+1=0 & exists(flted_36_55:0<=(flted_36_55+1)) & flted_37_1850+1=0 & 0<=(a_1842+1) & flted_55_1830=b_1841+0 & 0<=b_1841 & flted_55_1830=0 & b_1834=b_1835+0 & 0<=b_1835 & Anon_1833=Anon_1836 & 0<v_int_47_1832 & v_int_47_1832=1 & Anon_1836=Anon_1831 & 0<=b_1834 & 0<=1 & v_int_47_1832=b_1834+1 & v_int_47_1839=1 & 0<v_int_47_1839 & flted_55_1830=b_1841+flted_36_1840 & 0<=flted_36_1840 & flted_36_1840=0&{FLOW,(4,5)=__norm#E}[]
       es_ho_vars_map: [P --> h_40'::cell<Anon_13>&{FLOW,(4,5)=__norm#E}[]]

 ]

dprint: ex11a-cdl.ss:62: ctx:  List of Failesc Context: [FEC(0, 0, 1  [])]

Successful States:
[
 Label: []
 State:(exists flted_31_2033: h_40'::cell<Anon_13> * c_42'::CNT{}<flted_18_2042>*N@full[c_42,h_40,v_41,val_59_1435]&v_int_47_1665=b_1681+1 & 0<=b_1681 & Anon_11=Anon_12 & v_int_47_1665=1 & 0<v_int_47_1665 & Anon_13=Anon_11 & 0<=b_1810 & 0<=0 & b_1681=b_1810+0 & 0<1 & 0<=b_1742 & 1=b_1742+1 & flted_50_1743=1 & v_int_51_1740=1 & Anon_12=v_int_51_1740 & b_1744<flted_50_1743 & 0<n & 0<=n & 0<=b_1744 & flted_50_1743=b_1744+n & h_40'!=null & 0<=(a_1745+1) & flted_31_2033+1=n & 0<=(n+1) & flted_20_1759=flted_31_2033+b_1744 & flted_18_1854+1=0 & exists(flted_36_55:0<=(flted_36_55+1)) & flted_37_1957+1=0 & 0<=(a_1842+1) & flted_55_1830=b_1841+0 & 0<=b_1841 & flted_55_1830=0 & b_1834=b_1835+0 & 0<=b_1835 & Anon_1833=Anon_1836 & 0<v_int_47_1832 & v_int_47_1832=1 & Anon_1836=Anon_1831 & 0<=b_1834 & 0<=1 & v_int_47_1832=b_1834+1 & v_int_47_1839=1 & 0<v_int_47_1839 & flted_55_1830=b_1841+flted_36_1840 & 0<=flted_36_1840 & flted_36_1840=0 & v_41'=1+Anon_13 & flted_18_2038+1=0 & c_42'=c_42' & flted_18_2042+1=0&{FLOW,(4,5)=__norm#E}[]

*/
