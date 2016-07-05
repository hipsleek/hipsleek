
// immutable string
str join(str x,str y) 
   requires true
   ensures res=x^y;
{
  return x^x;
}
