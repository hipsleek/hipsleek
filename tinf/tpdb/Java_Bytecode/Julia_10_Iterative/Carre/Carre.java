class Curseur{
	private int X=0, Y=0, maxX, maxY;
	private boolean torique=false;

	public Curseur(int maxX, int maxY, boolean espaceTorique){
		super();
		this.maxX=maxX;
		this.maxY=maxY;
		this.torique=espaceTorique;		
	}

	public void centrer(){
		
			int cX=maxX/2;
			int cY=maxY/2;
			X=cX;
			Y=cY;
		
	}

	public void haut(){

			Y--;
			if(torique&&Y<0) Y=maxY-1;
	}

	public void bas(){
			Y++;
			if(torique&&Y==maxY) Y=0;
	}

	public void droite(){
			X++;
			if(torique&&X==maxX) X=0;
	}

	public void gauche(){
			X--;
			if(torique&&X<0) X=maxX-1;
	}

	public int getX(){
			return X;
	}

	public int getY(){
			return Y;
	}
	
	public void imprimer(){
	    //System.out.println("Curseur@["+getX()+","+getY()+"]");
	}
}

public class Carre {

	private Curseur curseur=null;
	private int cote=0;

	public Carre(int cote){
		if(cote>1&cote%2==1){
			this.cote=cote; 
		}else{
		    //System.out.println("Cette classe ne genere pas les carres magiques d\'ordre pair.");
		    //System.exit(0);
		}
		this.curseur=new Curseur(cote,cote,true);
	}
	
	private int [][] carre=null;

	public void init(){
		carre=new int[cote][cote];
		int n=0;
		for(int x=0;x<3;x++) for(int y=0;y<3;y++) carre[x][y]=0;
		curseur.centrer();
	}

	public void peupler(){
		curseur.bas();
		int nbre=1;
		int cpteur=1;
		while(cpteur<3){			
			if(!ajouter(nbre,curseur.getX(),curseur.getY())){
				curseur.bas();
				curseur.gauche();
				cpteur++;
			}else{
				cpteur=1;
				curseur.bas();
				curseur.droite();
				nbre++;
			}
		}
	}

	public Curseur curseur(){
		return curseur;
	}

	public int cote(){
		return cote;
	}

	public boolean ajouter(int nombre, int X, int Y){
		if(carre[X][Y]!=0) return false; 
		carre[X][Y]=nombre;
		return true;
	}

	public void imprimer(){
		for(int j=0;j<cote;j++){
			for(int i=0;i<cote;i++){
			    //System.out.print(carre[i][j]+"\t");
			}
			//System.out.println();
		}
	}

	public static void main(String args[]){
	    Random.args = args;
	    Carre carre=new Carre(2*Random.random()+1);
	    carre.init();
	    //carre.peupler();
	    carre.imprimer();
	}
    
}