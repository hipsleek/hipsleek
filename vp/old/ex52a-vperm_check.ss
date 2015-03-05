/*
  Checking for variable permissions 
  in the presence of concurrent threads.
 */

data cell{
  int val;
}

//valid
void inc(ref int i)
  requires @full[i] //
  ensures @full[i] & i'=i+1; //; //' check for VPERM only
{
  i++;
}

void incCell(ref cell x)
  requires x::cell<i> * @full[x] //& @full[x]
  ensures  x::cell<i+1> * @full[x] & x'=x; //& @full[x]; //check for permission only
{
  x.val++;
}

//fail
int test1(ref int x,ref int y)
  requires @full[x,y] //
  ensures @full[y] & res = z & y'=y+1 
          and thread=z & true--> @full[x] & x'=x+1; //'
{
  int id;
  id=fork(inc,x);
  //x = 0; // --> No permission -> cannot assign to x
  inc(y);
  dprint;
  return id;
}

/*
# ex52a-vperm_check.ss

Why did we have x'=1+x+_1450 which contradicts with x'=x_1450?
WHere is @full[x]?

Successful States:
[
 Label: []
 State:htrue*N@full[id_37,y]@zero[x]&y'=1+y & id_37'=tid_1449 & x_1450=x&{FLOW,(4,5)=__norm#E}
AND  <thread=tid_1449>  <delayed:true>  <ref:[x]> emp&x'=1+x_1450

 ]

*/
