void main ()
requires Loop
ensures false;
{
	int choose = 2;
	int life = 13;
	int death = 17;

	loop(choose, life, death);
}

void loop (ref int choose, ref int life, ref int death)
case {
	life>=death -> requires Term ensures true;
	life<death -> case {
		choose>=life+1 -> requires Term ensures true;
		choose<life+1 -> requires Loop ensures false;
	}
}
{
	if (life < death) {
		int temp = death;
		death = life + 1;
		life = temp;

		if (choose < life || choose < death)
			life = choose;

		loop(choose, life, death);
	}
}
