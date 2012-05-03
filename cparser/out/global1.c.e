
global int x;

int main()
requires true
ensures x'=x+1 & res=0;
{
  x = x+ 1;
  //printf("Hello world\n");
  return 0;
}
