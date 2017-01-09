

data ChooseLife
{

}
 void ChooseLife_main(String[] args)
{
  int choose = 2;
  int life = 13;
  int death = 17;
  while (life < death) {
    int temp = death;
    death = life + 1;
    life = temp;
    if (choose < life || choose < death)
      life = choose;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;