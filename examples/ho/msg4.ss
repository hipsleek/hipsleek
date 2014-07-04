data cell {
  int x;
}

data chan {
  int y;
}

pred_prim MSG{F}<c:cell>
inv c!=null;

pred_prim CNT<i:int>
inv true;

// "chan" type lost?
// what is the type for res in res::MSG{v::cell<1> & true}<v>?
chan create_msg (int x)
  requires true
 ensures res::MSG{(exists n: v::cell<n> & n>x)}<v> * res::CNT<0>;
// ensures (exists v: res::MSG{(exists n: v::cell<n> & n>x)}<v> * res::CNT<0>);

/*
chan create_msg{%G}(int x)
  requires true ensures (exists v: res::MSG{%G}<v>);
*/

void send(chan ch, cell c)
  requires ch::MSG{%P}<c>@L * %P * ch::CNT<n>
  ensures ch::CNT<n+1>;

void receive(chan ch, ref cell c)
  requires ch::MSG{%P}<c>@L * ch::CNT<n> & n>0 // do we use c or c'??
  ensures  %P * ch::CNT<n-1> & c'=c;

void main() 
 requires true
 ensures true;
{
  chan ch = create_msg(5);
  dprint;
  cell c = new cell(10);
  dprint;
  cell d,d2;
  dprint;
  send(ch,c);
  dprint;
  cell c2 = new cell(7); // false state induced when 6 change to 7.
  dprint;
  send(ch,c2);
  dprint;
  receive(ch,d);
  dprint;
  receive(ch,d2);
  dprint;
}

/*
# msg4.ss

n_1300 should be existentially quantified..

Instead of:
  (exists v,n: res::MSG{v::cell<n> & n>x}<v>

We need quantification within the CAP 
  res::MSG[v,n]{v::cell<n> & n>x}<v>

  (exists v,n:   res::MSG{v::cell<n> & n>x}<v> * res::CNT<0>);


 State:(exists flted_19_1284,v_1285,n_1286,v_int_38_1200': 
  ch_38'::MSG{v_1285::cell<n_1286>&v_int_38_1200'<n_1286&{FLOW,(24,25)=__norm}[]}<v_1285> 
* ch_38'::CNT{}<flted_19_1284>
 &v_int_38_1200'=5 & flted_19_1284=0&{FLOW,(24,25)=__norm})[]

 State:(exists flted_32_1344: ch_38'::MSG{ v_1299::cell<n_1300>&v_int_38_1301<n_1300&{FLOW,(24,25)=__norm}[]}<v_1299> 
* d_40'::cell<n_1300> * ch_38'::CNT{}<flted_32_1344> * d2_41'::cell<n_1300>&0<n_1322 & c_39'=v_1320 & v_int_38_1301<n_1300 & c_39'=v_1305 & v_int_38_1301<n_1300 & c_39'=v_1320 & v_int_38_1301<n_1300 & c_39'=v_1305 & v_int_38_1301<n_1300 & c_39'=v_1305 & v_int_38_1301<n_1300 & v_int_38_1301=5 & flted_19_1298=0 & v_int_40_1302=6 & n=flted_19_1298 & n_1300=v_int_40_1302 & c_1308!=Cnull & flted_28_1316=1+n & c_1308!=Cnull & v_int_45_1317=6 & n_1309=flted_28_1316 & n_1300=v_int_45_1317 & c_39'!=Cnull & flted_28_1328=1+n_1309 & c_39'!=Cnull & n_1322=flted_28_1328 & flted_32_1340+1=n_1322 & d_40'!=Cnull & v_int_38_1301<n_1300 & n_1334=flted_32_1340 & flted_32_1344+1=n_1334 & d2_41'!=Cnull & v_int_38_1301<n_1300&{FLOW,(24,25)=__norm})[]

 Label: []
 State:(exists n_1347,flted_33_1346: ch_38'::MSG{ (exists n: v_1291::cell<n>&v_int_39_1292<n&{FLOW,(24,25)=__norm})[]}<v_1291> * 
d_40'::cell<n_1341> * ch_38'::CNT{}<flted_33_1346> * 
d2_41'::cell<n_1347>&0<n_1321 & c2_42'=v_1316 & v_int_39_1292<v_int_46_1312 & c_39'=v_1297 & v_int_39_1292<v_int_41_1293 & c2_42'=v_1316 & v_int_39_1292<v_int_46_1312 & c_39'=v_1297 & v_int_39_1292<v_int_41_1293 & c_39'=v_1297 & v_int_39_1292<v_int_41_1293 & v_int_39_1292=5 & flted_19_1290=0 & v_int_41_1293=6 & n=flted_19_1290 & c_39'!=Cnull & flted_29_1311=1+n & c_39'!=Cnull & v_int_46_1312=7 & n_1304=flted_29_1311 & c2_42'!=Cnull & flted_29_1327=1+n_1304 & c2_42'!=Cnull & n_1321=flted_29_1327 & flted_33_1342+1=n_1321 & d_40'!=Cnull & v_int_39_1292<n_1341 & n_1334=flted_33_1342 & flted_33_1346+1=n_1334 & d2_41'!=Cnull & v_int_39_1292<n_1347&{FLOW,(24,25)=__norm})[]


 ]

parser problem with "chann as result"

P should be free:
         EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume 
                    (exists P: HVar P&{FLOW,(24,25)=__norm})[]
                    



*/
