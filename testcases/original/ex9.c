//Ex 10
#include <string.h>
#include <stdlib.h>

int main()
{
       FILE *fp = fopen("good.c", "r");
       fclose(fp);

       int i = 0;
       char c = getc(fp);
       printf("%s/n",c);
       return 0;
}
