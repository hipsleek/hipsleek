/*

this example requires variable permission to
model properly

demo/vperm/vperm_check.ss:  ensures @full[y] & res = z
demo/vperm/vperm_check.ss:          and @full[x] & thread=z; //'

examples/fracperm/var-lock2.ss:      => lock it (with @full in the invariant)
examples/fracperm/var-lock2.ss:    + @full for all local vars
examples/fracperm/var-lock2.ss:inv(l) := @full(x,y,z) & x=y+z
examples/fracperm/var-lock2.ss:  //{@full(x,y,z) & x=y+z & y=0}
examples/fracperm/var-lock2.ss:  //{@full(x,y,z) & x+1=y+z & y=1}

*/

void inc(ref int i, int j)
   requires @full[i] * @val[j] 
   ensures  @full[i] & i'=i+j
{ 
   i = i+j;
}


int creator(ref int x, ref int y)
  requires @full[x,y]
  ensures (@full[y] & y'=y+2) * res::thread{@full[x] & x'=x+1}<>;
{
  int tid = fork(inc,x,1);
  inc(y,2);
  return tid;
}

void main()
{
  int id;
  int x = 0; y=0;
  id = creator(x,y);
  join(id);
  assert(x'+y'=3);
}
