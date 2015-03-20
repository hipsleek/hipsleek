

data MirrorIntervSim
{

}
 void MirrorIntervSim_loop(int i)
{
  while (i != 0) {
    if (-5 <= i && i <= 35) {
      if (i < 0) {
        i = -5;
      } else {
        if (i > 30) {
          i = 35;
        } else {
          i--;
        }
      }
    } else {
      i = 0;
    }
  }
}



data Main
{

}
 void Main_main(String[] args)
{
  MirrorIntervSim_loop(args.length);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;