/*
  Checking for variable permissions 
  in the presence of concurrent threads.
 */
pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

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

Thrd fork_inc(ref int i)
  requires @full[i] //@full[i]
  ensures res::Thrd{+@full[i] & i'=i+1}<>; //@full[i]; //' check for VPERM only

Thrd fork_incCell(ref cell x)
  requires  x::cell<i> * @full[x]  //& @full[x]
                                                                             ensures  res::Thrd{+x::cell<i+1> * @full[x] & x'=x}<>; //'

void incCell(ref cell x)
  requires  x::cell<i> * @full[x]  //& @full[x]
  ensures  x::cell<i+1> * @full[x] & x'=x ; //& @full[x]; //check for permission only
{
  x.val++;
}


//fail
Thrd test1(ref int x,ref int y)
  requires true //@full[x,y]
  ensures res::Thrd{+@full[x]}<> * @full[y];
{
  Thrd id;
  id=fork_inc(x);
  x = 0; // --> No permission -> cannot assign to x
  inc(y);
  return id;
}

//fail
Thrd test2(ref cell x,ref cell y)
  requires x::cell<i> * y::cell<j> * @full[x,y] // & @full[x,y] 
  ensures res::Thrd{+ x::cell<i+1> * @full[x]}<>*y::cell<j+1> * @full[y] ;
{
  Thrd id;
  id=fork_incCell(x);
  y.val ++;
  x.val++; // --> No permission -> cannot access its field
  return id;
}

//fail
Thrd test3(ref int x,ref int y)
  requires @full[x,y] //@full[x,y]
  ensures res::Thrd{+
         @full[x]}<> 
    * @full[y] ;
{
  Thrd id;
  id=fork_inc(x);
  y = x; // --> No permission -> cannot read x
  inc(y);
  return id;
}

//fail
int test4(ref int x,ref int y)
  requires @full[x,y] //@full[x,y]
  ensures @full[y] & res = z
          and thread=z & true --> @full[x]; //'
{
  int id;
  id=fork(inc,x);
  inc(y);
  return x; // --> No permission -> cannot return x
}
