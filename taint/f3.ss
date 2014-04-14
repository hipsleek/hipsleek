int main(int l1, int l2, int h1, int h2)
  requires l1=l2
  ensures res=1;
{
  // Original
  l1 = l1 + h1;
  if( h1 != 0 ) { l1 = l1 - h1; }
  if( l1 >  0 ) { if( l1 % 2 == 1 ) { l1 = l1 - 1; } }

  // Primed
  l2 = l2 + h2;
  if( h2 != 0 ) { l2 = l2 - h2; }
  if( l2 >  0 ) { if( l2 % 2 == 1 ) { l2 = l2 - 1; } }

  //assert l1'=l1;
  // Check
  if( l1 == l2 ) { return 1; }
  else { 
    dprint;
    return 0; 
  }
}
