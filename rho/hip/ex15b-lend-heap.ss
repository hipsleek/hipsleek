data cell { int val; }

void main()
  requires emp ensures emp;
{
  cell x = new cell(1);
  int y = 1;
  int z = 2;
  //dprint;
  par {x,y@L,z}
  {
     case {x,y@L} x'::cell<_> ->
       dprint;
       x.val = y + x.val;
       dprint;
  || 
     //case {y@L,z} emp ->
     else ->
       z = z + y;
       dprint;
  }
  dprint;
  assert x'::cell<2> & y'=1 & z'=3;
  assert x'::cell<3> & y'=1 & z'=3;
  assert x'::cell<3> & y'=1 & z'=4;
  assert x'::cell<3> & y'=0 & z'=4;
}

/*
# ex15b

 State:(exists v_int_14_1493,x_1494,z_1492: x_1494::cell<v_int_6_1435> * x_38'::cell<v_int_14_1493>*@full[y_39,val_14_1369,x_38,val_14_1363,z_40]&z_1492=2 & y_39'=1 & v_int_6_1435=1 & z_1460=2 & v_int_6_1461=1 & z_14

*/
