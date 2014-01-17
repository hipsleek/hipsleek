int foo(bool flag)
  requires true
  ensures flag & res=1 or !(flag) & res=2;
{
  if (flag) return 1;
  else return 2;
} 


string foo2(bool flag)
  requires true
  ensures flag & res="1" or !(flag) & res="2";
{
  if (flag) return "1";
  else return "2";
} 
