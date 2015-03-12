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
 ensures  @full[i] & i'=i+1; //'@full[i] &
{
  i++;
}
