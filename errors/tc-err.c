global int globA;
global int globB;


int alt()
  /* requires  true */
  /* ensures  true; */
{
  int a = globA+1;
  return a;
}


int main(int argc /*argv,*/)
  requires  true
  ensures  true;
{

    if(argc < 13)
    { 

	return 1;
    }
    assume(globB >= 0 & globB <=3);
    alt();
    return 0;
}
