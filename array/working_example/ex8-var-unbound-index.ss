relation P(int a_i,int i).
  relation Q(int a_i,int a_i_p,int i,int i_p).

  void foo(ref int a_i, ref int i)
  infer [Q] requires true ensures Q(a_i,a_i',i,i');
{
   if(i<10){
      a_i = 10;
      i = i+1;
      foo(a_i,i);
      return;
   }
   else{
     return;
   }

}
