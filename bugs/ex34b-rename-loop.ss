/* void main () { */
/*  int x=1; */
/*  { */
/*    int x = x; */
/*    x=x+1; */
/*  } */
/* } */

/* void one(){ */
/*   int x=1; */
/*   int y=2; */
/*   { */
/*     int x=y; */
/*     int y=2; */
/*     x = x + y; */
/*   } */
/* } */

/* void two(){ */
/*   int x=1; */
/*   int y=2; */
/*   { */
/*     int x=y; */
/*     x = x+y; */
/*   } */
/* } */

void three(){
  int x=1;
  int y=2;
  {
    int x=y;
    x = x+y;
    {
      int x=x;
      int y=y;
      y = y+x;
    }
  }
}


/*
# ex34b

renaming incorrect..

rename_exp@1
rename_exp inp1 :{local: int x
int x;
{local: int x
int x = x}}
rename_exp inp2 :[]
rename_exp@1 EXIT:{local: int x
int x;
{local: int x_14
int x_14 = x_14}}



 int x=1;
 {int x2 = x
 {
  int x = x2;
  x=x+1;
 }
}

*/
