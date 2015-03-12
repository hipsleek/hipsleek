/*--ann-vp

  Description: fairly complicated inter-procedural passing 
  of stack variables between concurrent threads

 */

void inc(ref int i)
 requires @full[i]
 ensures  @full[i] & i'=i+1; //'@full[i] &
{
  i++;
}

void inc2(int i)
 requires @value[i]
 ensures  @full[i] ; //'@full[i] &
{
  i++;
}
/* 
# ex35a --ann-vp
# inc2
  should not allow @full[i] to escape method

*/

void inc3(int i)
 requires @value[i]
 ensures  @full[i] ; //'@full[i] &
{
  dprint;
  inc2(i);
  inc2(i);
  assert false;
  dprint;
}
