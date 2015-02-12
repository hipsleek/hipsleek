void main () {
 int x;
 {
  int x = x;
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
