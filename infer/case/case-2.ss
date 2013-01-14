void foo(ref int x)
  requires x>=0
  ensures 
    case {
     x'=1 -> true;
     x'!=1 -> x'>1;
    };
{
  x=x+1;
}

