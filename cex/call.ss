

void main()
  requires Term[]
  ensures true;
{
  aux();
}

void aux()
  requires Term[]
  ensures true;
{
  int x;
  x=0;
  main();
}

