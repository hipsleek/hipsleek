/*class ret_int extends __Exc{
  int val
} //exception when return from a loop
*/

int  test_int(int a)
requires true
 ensures  res=2;
{
  while (a>1) 
    requires true
    ensures  true;
  {
    a--;
  }

  return 2;
  //dprint;
}

/*
# test2f.ss

No need for while-ret try-catch here.

{({f_r_1271_while_12_2$int(a)};
(int v_int_18_1280;
(v_int_18_1280 = 2;
ret# v_int_18_1280)))}
 catch (23,24)=ret_int ret_int:f_r_1268 ) 
	(int v_int_11_1270;
(v_int_11_1270 = bind f_r_1268 to (val_11_1269) [read] in 
val_11_1269;
ret# v_int_11_1270))


*/
