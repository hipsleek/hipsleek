public class ChooseLife {
    public static void main(String[] args) {
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
}