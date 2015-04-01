
global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  if (Random_index >= Random_args.length)
    return 0;
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}



data Curseur
{
int X = 0;

int Y = 0;

int maxX;

int maxY;

boolean torique = false;
}
 void Curseur_centrer(Curseur _this)
{
