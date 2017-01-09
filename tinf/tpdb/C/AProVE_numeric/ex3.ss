int rec1(int i) 
  //infer [@post_n,@term]
  //requires true
  //ensures true;
{
	if(i <= 0)
		return 0;
	return rec1( rec1( rec1(i-2) - 1 )) + 1  ;	
}

int rec2(int j) 
  //infer [@term]
  //requires true
  //ensures true;
{
	if(j <= 0)
		return 0;
	return rec2(rec1(j+1)) - 1;
}

int main() 
  //infer [@term]
  //requires true
  //ensures true;
{
	int x = __VERIFIER_nondet_int();
	rec1(x);
}
