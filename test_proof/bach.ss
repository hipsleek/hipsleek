void bach(ref int x, ref int y, ref int z, ref int k)
  requires x>2 & y>2 & z>2 & k>2
  ensures y'=y+2 & z'=z+2 & x'=x+2 & k'=k+2;
{
        x=x+1;
        y=y+1;
        z=z+1;
        k=k+1;
        x=x+1;
        y=y+1;
        z=z+1;
        k=k+1;
        bool b1 = x>4;
        bool b2 = y>4;
        bool b3 = z>4;
        bool b4 = k>4;
        if (b1)
           {
             x=x+1;
             y=y+1;
             z=z+1;
             k=k+1;
            if (b2) {
             x=x-1;
             y=y-1;
             z=z-1;
             k=k-1;
              if (b3) {
             x=x+1;
             y=y+1;
             z=z+1;
             k=k+1;
              if (b4) {
             x=x-1;
             y=y-1;
             z=z-1;
             k=k-1;
              }
             }
            }
           }
}
