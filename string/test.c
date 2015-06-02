 # include <stdio.h>

    char* cstrcat(char *s, const char *append)
      {
       char *save = s;
       //if (*s) {printf("exit\n"); return append;};
       for (; *s; ++s);
       while ((*s++ = *append++) != '\0');
      return(save);
      }

int main()
{
  printf("Hello world\n");
  char t1[100]="Hi ";
  char *t2="There";
  printf("(%s) (%s)\n", t1,t2);
  printf("Before cstrcat");
  char *t3=cstrcat(t1,t2);
  printf("After cstrcat");
  printf("(%s) (%s) (%s)\n", t1,t2,t3);
  return 0;

}

/*
# test.c

# there seems a core dump..

Hello world
(Hi ) (There)
Segmentation fault (core dumped)

*/
