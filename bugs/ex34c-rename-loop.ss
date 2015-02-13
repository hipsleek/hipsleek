void main () {
  int x=1; int y=3;
 {
  int x = y;
  int y = x;
  x=x+y;
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
*/
