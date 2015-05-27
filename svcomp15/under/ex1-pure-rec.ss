void foo(){
  int t = goo(2);
 
  assert(t<0);
}

void goo(int b){
  if (b=0) return 0;
  else return 1+goo(b-1);
}

/*
goo(b,res) == b=0 & res=0
  or exists r. goo(b-1,r) & res=r+1;
*/
