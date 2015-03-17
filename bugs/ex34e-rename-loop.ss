void main () {
 int x=1;
 {
   int x = x;
   x = x+1;
   { int x = x;
     x = x+1;
   }
   x=x+1;
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
