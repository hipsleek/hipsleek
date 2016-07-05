// Given a method where i,j are in-out parameters.
// write the strongest postcondition involving i,j,i',j'
// for swap method below
void swap (ref int i, ref int j)
  requires true 
  ensures true;
{
  int c=i;
  i=j;
  j=c;  
}
