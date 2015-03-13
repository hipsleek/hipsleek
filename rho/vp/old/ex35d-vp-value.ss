
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

void inc2(ref int i)
 requires @full[i]
 ensures  i'=i+1; //'@full[i] &
// classic triggers memory leak
{
  i++;
}

void inc3(int i)
 requires @full[i]
 ensures  true; //'@full[i] &
{
  i++;
}

void inc4(int i)
 requires @value[i]
 ensures  true; //'@full[i] &
{
  i++;
}

void inc5(int i)
 requires @value[i]
 ensures  @full[i]; //'@full[i] &
{
  i++;
}
