void bach3(ref int x, ref int y, ref int z) //change the number of variables
  requires x>2 & y>2 & z>2 //no change 2
  ensures y'=y+3 & z'=z+3 & x'=x+3; //change 
{
        x=x+1;
        y=y+1;
        z=z+1;
        x=x+1;
        y=y+1;
        z=z+1;
        bool b1 = x>4;//no change 4
        bool b2 = y>4;
        bool b3 = z>4;
        if (b1)
           {
             x=x+1;
             y=y+1;
             z=z+1;
            if (b2) {
             x=x-1;
             y=y-1;
             z=z-1;
              if (b3) {
             x=x+1;
             y=y+1;
             z=z+1;
             }
            }
           }
}
