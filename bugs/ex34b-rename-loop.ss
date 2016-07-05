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

ERROR: at ex34b-rename-loop.ss_4:11_4:12
Message: x_14, line 4, col 11 is used before declared

int x = 1;
{local: int x_14
int x_14 = x_14;
x_14 = x_14 + 1}}

int x = 1;
{local: int x_14
int x_14 = x;
x_14 = x_14 + 1}}

{local: int x;
int x = x;
x_14 = x_14 + 1}}


*/
