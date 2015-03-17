/*
  General high-order primitives for threads.

  A thread carrying a cell
 */

data cell{
  int v;
}

pred_prim THRD{(-)P,(+)Q}<x:cell,y:cell>
inv x!=null;

pred_prim THRD2{(+)Q@Split}<x:cell,y:cell>
inv x!=null;

pred_prim THRD3{(-)P,(+)Q}<t:thrd, x:cell>
inv x!=null;

pred_prim THRD4{(+)Q}<t:thrd, x:cell>
inv x!=null;

//after join
pred_prim DEAD<>
inv true;

/*
lemma t::THRD2{%P * %Q}<x> -> t::THRD2{%P}<x> * t::THRD2{%Q}<x>;
lemma t::THRD2{%P}<x> & t::DEAD<> -> %P;
*/

//this new thread multiplies x and y by 10
thrd create_thrd() // with %P
  requires true
  ensures (exists x,y: res::THRD{x::cell<vx> * y::cell<vy> & true,x::cell<vy> * y::cell<vx>}<x,y>);

void fork_thrd(thrd t,cell x, cell y)
  requires t::THRD{%P,%Q}<x,y> * %P
  ensures  t::THRD2{%Q}<x,y>;

void join_thrd(thrd t)
  requires exists x,y: t::THRD2{%Q}<x,y>
  ensures  t::DEAD<> * %Q;

// this new thread adds 3 to x
thrd create_thrd2() // with %P
  requires true
  ensures (exists x,t,y: res::THRD3{ t::THRD2{x::cell<vx>}<x,y> & true,x::cell<vx+1>}<t,x>);

void fork_thrd2(thrd t2,thrd t, cell x)
  requires t2::THRD3{%P,%Q}<t,x> * %P
  ensures  t2::THRD4{%Q}<t,x>;

void join_thrd2(thrd t2)
  requires exists t,x: t2::THRD4{%Q}<t,x>
  ensures  t2::DEAD<> * %Q;

void destroy(cell c)
  requires c::cell<_>
  ensures emp;

void main()
  requires emp ensures emp;
{
  cell x = new cell(1);
  cell y = new cell(2);

  thrd tid1 =  create_thrd();
  thrd tid2 =  create_thrd2();

  fork_thrd(tid1,x,y); //(x=1,y=2) -> (x=2,y=1)
  fork_thrd2(tid2,tid1,x);

  join_thrd(tid1);

  y.v = y.v +2; //y=3

  join_thrd2(tid2); //x=3


  assert x'::cell<3> * y'::cell<3>;
  destroy(x);
  destroy(y);
 
}


/*

 State:tid2_43'::THRD3{ t_1294::THRD2{ (exists flted_48_50: x_1293::cell<flted_48_50>&flted_48_50=10&
{FLOW,(24,25)=__norm})[]}<x_1293,y_1295>&
{FLOW,(24,25)=__norm}[],
(exists flted_48_51: x_1293::cell<flted_48_51>&flted_48_51=13&
{FLOW,(24,25)=__norm})[]}<t_1294,x_1293>

* tid1_42'::THRD2{ (exists flted_35_1306,flted_35_1307,x_1308,
y_1309: x_1308::cell<flted_35_1307> * y_1309::cell<flted_35_1306>&
x_40'=x_1308 & y_41'=y_1309 & flted_35_1307=10 & flted_35_1306=20&
{FLOW,(24,25)=__norm})[]}<x_40',y_41'>

&v_int_60_1271=1 & v_int_61_1272=2 & y_41'!=Cnull & x_40'!=Cnull & x_1278!=Cnull & x_40'!=Cnull&{FLOW,(24,25)=__norm}[]



 es_formula: 
  tid1_42'::THRD2{ (exists flted_35_1306,flted_35_1307,x_1308,
y_1309: x_1308::cell<flted_35_1307> * y_1309::cell<flted_35_1306>&
x_40'=x_1308 & y_41'=y_1309 & flted_35_1307=10 & flted_35_1306=20&
{FLOW,(24,25)=__norm})[]}<x_40',y_41'>&
  x_40'=x_1298 & y_41'=y_1299 & v_int_60_1271=1 & v_int_61_1272=2 & 
  v_int_60_1271=1 & v_int_61_1272=2 & y_41'!=Cnull & x_40'!=Cnull & 
  x_1278!=Cnull & x_40'!=Cnull&{FLOW,(24,25)=__norm}[]

|-
 t_1316::THRD2{ (exists flted_48_50: x_1317::cell<flted_48_50>&flted_48_50=10&
{FLOW,(24,25)=__norm})[]}<x_1317,y_1295>&
tid1_42'=t_1316 & x_40'=x_1317&{FLOW,(24,25)=__norm}[]


id2_43'::THRD3{ t_1294::THRD2{ (exists flted_48_50: x_1293::cell<flted_48_50>&flted_48_50=10&
{FLOW,(24,25)=__norm})[]}<x_1293,y_1295>&
{FLOW,(24,25)=__norm}[], (exists flted_48_51: x_1293::cell<flted_48_51>&flted_48_51=13&
{FLOW,(24,25)=__norm})[]}<t_1294,x_1293>

|- 
 */
