//Ex 9: Use of expired file descriptor

int main()
{
  FILE *fp = fopen("good.c", "r");
  fclose(fp);

  int i = 0;
  char c = getc(fp);
  printf("%s/n",c);
  return 0;
}
