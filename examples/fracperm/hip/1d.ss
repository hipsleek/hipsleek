/* fork(id,method_name,single argument) */

data cell {
  int val;
}

void inc(cell x)
  requires x::cell<i>
  ensures x::cell<i+1> & flow __norm; //'
{
  x.val = x.val+1;
}


int test(cell x, cell y, int i)
  requires x::cell<i>* y::cell<j>
  ensures  (exists v: y::cell<j> & i>0 & res=v
            and x::<i+1> & thread=v & flow __norm)
           or (exists v: x::cell<i> & i <=0 & res=v
               and y::cell<j+1> & thread=v & flow __norm) ; //'
{
  int id;
  if (i>0){
    id = fork(inc,x);
  }else{
    id = fork(inc,y);
  }
  return id;
}

int main()
  requires true
  ensures res=1;
{
  cell x=new cell(0);
  cell y=new cell(0);
  int id;
  int flag=1;
  id = test(x,y,flag); //increase either x or y depending on flag
  join(id);
  return x.val+y.val;
}

