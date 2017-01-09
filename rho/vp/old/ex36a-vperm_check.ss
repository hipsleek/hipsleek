/*
  Checking for variable permissions 
  in the presence of concurrent threads.
 */

data cell{
  int val;
}

//valid
void inc(ref int i)
  requires @full[i] //@full[i]
  ensures @full[i] & i'=i+1; //@full[i]; //' check for VPERM only
{
  i++;
}

void incCell(ref cell x)
  requires  x::cell<i> * @full[x]  //& @full[x]
  ensures  x::cell<i+1> * @full[x] & x'=x ; //& @full[x]; //check for permission only
{
  x.val++;
}

