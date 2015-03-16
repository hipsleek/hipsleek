void main () {
  int x=1; int y=3;
 {
  int x = x;
  int y = y;
  x=x+y;
 }
}

/*
# ex34b

renaming incorrect..

rename_exp@1 EXIT:{local: int x,int y
int x = 1;
int y = 3;
{local: int x_14,int y_15
int x_14 = x_14;
int y_15 = y_15;
x_14 = x_14 + y_15}}


*/
