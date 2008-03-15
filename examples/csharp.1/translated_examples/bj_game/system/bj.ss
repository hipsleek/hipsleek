/* black jack game */

/* translation of the Card class (file Card.cs) */


/* constants (enum in C#) */
/* suits */
enum Suit {Diamonds, Spades, Clubs, Hearts}
/* card face values */
enum FaceValue {Two = 2, Three = 3, Four = 4, Five = 5, Six = 6, Seven = 7, Eight = 8, Nine = 9, Ten = 10, Jack = 11, Queen = 12, King = 13, Ace = 14}
/* default values */
enum Defaults {PlayerImage, PlayerName}


/* data type to store a card */
data Card{
	Suit suit; 
	FaceValue faceVal; 
	bool isCardUp; 
}  

/* function corresponding to the methods from the class Card */

/* set/get functions */
/* get suit */
Suit get_suit(Card card)
{
	return card.suit;
}

/* get faceVal */
FaceValue get_faceVal(Card card)
{
	return card.faceVal;
}

/* get/set for isCardUp */
bool get_isCardUp(Card card)
{
	return card.isCardUp;
}

void set_isCardUp(Card card, bool value)
{
	card.isCardUp = value;
}

/* constructor */
Card Card1(Suit suit, FaceValue faceVal, bool isCardUp)
{
	return new Card(suit, faceVal, isCardUp);	
}

////////////////////////////////////////////////
//////// this will be in a separate file ///////
////////////////////////////////////////////////
data List {
	Card inf; 
	Node next;
}

/* function to return the number of nodes of a List */
int count(List l)
{
	int c = 0;
	List tmp = l;

	while (tmp != null)
	{
		c++;
		tmp = tmp.next;
	}

	return c;
}

/* get the ith element from a list */
Card get_ith(List l, int i)
{
	List tmp = l;
	int n = count(l);

	/* if i is negative or is greater that the size of the list */
	if (i < 0 || i >= n) 
		return null;
	while  (i > 0)
	{
		tmp = tmp.next; 
		i -= 1;
	}

	return tmp;
}

/* add an element to a list of Cards (at the end) */
void add(List l, Card c)
{

	if (l == null)
		return new List(c, null); 

	while (l.next != null)
		l = l.next;
	
	l.next = new List(c, null);
}

void removeAt(List l, int i);

void set_ith(List l, int i, Card value);

int random();

int random2(int n);

int compareTo(int a, int b); 

void error();

////////////////////////////////////////////////
////////////////////////////////////////////////

/* data type to store a deck */
data Deck{
	List cards;
}  

/* function corresponding to the methods from the class Card */

/* set/get functions */
/* there is get_ith corresponding to the list */

/* constructor (one complete deck) */ 
Deck Deck1()
{
	List cards; 

	add(cards, new Card(Suit.Diamonds, FaceValue.Two, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Three, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Four, true));
	add(cards, new Card(Suit.Suit.Diamonds, FaceValue.Five, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Six, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Seven, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Eight, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Nine, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Ten, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Jack, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Queen, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.King, true));
	add(cards, new Card(Suit.Diamonds, FaceValue.Ace, true));

	add(cards, new Card(Suit.Spades, FaceValue.Two, true));
	add(cards, new Card(Suit.Spades, FaceValue.Three, true));
	add(cards, new Card(Suit.Spades, FaceValue.Four, true));
	add(cards, new Card(Suit.Spades, FaceValue.Five, true));
	add(cards, new Card(Suit.Spades, FaceValue.Six, true));
	add(cards, new Card(Suit.Spades, FaceValue.Seven, true));
	add(cards, new Card(Suit.Spades, FaceValue.Eight, true));
	add(cards, new Card(Suit.Spades, FaceValue.Nine, true));
	add(cards, new Card(Suit.Spades, FaceValue.Ten, true));
	add(cards, new Card(Suit.Spades, FaceValue.Jack, true));
	add(cards, new Card(Suit.Spades, FaceValue.Queen, true));
	add(cards, new Card(Suit.Spades, FaceValue.King, true));
	add(cards, new Card(Suit.Spades, FaceValue.Ace, true));

	add(cards, new Card(Suit.Hearts, FaceValue.Two, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Three, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Four, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Five, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Six, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Seven, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Eight, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Nine, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Ten, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Jack, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Queen, true));
	add(cards, new Card(Suit.Hearts, FaceValue.King, true));
	add(cards, new Card(Suit.Hearts, FaceValue.Ace, true));

	add(cards, new Card(Suit.Clubs, FaceValue.Two, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Three, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Four, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Five, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Six, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Seven, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Eight, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Nine, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Ten, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Jack, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Queen, true));
	add(cards, new Card(Suit.Clubs, FaceValue.King, true));
	add(cards, new Card(Suit.Clubs, FaceValue.Ace, true));

	return new Deck(cards);
}

/* draw a card from the deck */
Card draw(Deck deck)
{
	Card card = get_ith(deck.cards, 0);
	removeAt(deck.cards, 0);

	return card;
}
 
/* swap two cards from the deck */
void swapCard(Deck deck, int index1, int index2)
{
	Card card = get_ith(deck.cards, index1);
	set_ith(deck.cards, index1, get_ith(deck.cards, index2));
	set_ith(deck.cards, index2, card);	
}

/* shuffle the cards in the deck */
void shuffle(Deck deck)
{
	int random = random(), i = 0;
	
	while (i < count(deck.cards))
	{
		int index1 = i; 
		int index2 = random2(count(deck.cards));
		swapCard(deck, index1, index2);
		i++; 
	}
}

/* data to store a black jack hand */
data Hand{
	List cards;
	int numCards; 
}

/* constructor --> corresponding to the implicit one */
void Hand1()
{
	return new Hand(null, 0);
}

/* get/set functions */
/* numCards */
int get_numCards(Hand hand)
{
	return hand.numCards; 
}

/* cards */
List get_cards(Hand hand)
{
	return hand.cards;
}

/* function to see if a card is contained in the list */
bool containsCard(Hand hand, FaceValue item)
{
	int i = 0, n = count(hand.cards); 
	Card c;

	while (i < n)
	{
		c = get_ith(hand.cards);
		if (c.faceVal == item)
			return true;
	}	

	return false;
}

/* gets the total value of a hand from blackjack values */
int getSumOfHand(Hand hand)
{
	int val = 0, numAces = 0;
	Card c;

	while (i < n)
	{
		c = get_ith(hand.cards);
		if (c.FaceVal == FaceValue.Ace)
		{
			numAces++;
			val += 11;
		}
		else
		{
			 if (c.faceVal == FaceValue.Jack || c.faceVal == FaceValue.Queen || c.faceVal == FaceValue.King)
				val += 10;
			 else 
				val += c.FaceVal;
		}
		i++;
	}

	while (val > 21 && numAces > 0)	
	{
		val -= 10;
		numAces--; 
	}

	return val;
	
}

/* function to compare 2 blackjack hands */
int compareFaceValue(Hand otherHand)
{
	if (otherHand != null)
		return compareTo(getSumOfHand(hand), getSumoOfHand(otherHand));
	else
		error();     // this corresponds to throwing an exception 		
}


data String {
	int value;
}

/* data to store information about a player (Player.cs) */
data Player {
	float balance;
	Hand hand; 
	float bet;
	int wins;
	int losses;
	int pushes;
	String image;
	String name;
	Deck currentDeck; 
	List cards;
}

/* set/get functions */
/* current deck */
Deck get_currentDeck(Player player)
{
	return player.currentDeck; 
}

void set_currentDeck(Player player, Deck value)
{
	player.currentDeck = value; 
}

/* image */
String get_image(Player player)
{
	return player.image;
}

void set_image(Player player, String value)
{
	player.image = value;
}

/* hand */
Hand get_hand(Player player)
{
	return player.hand;
} 

/* name */
String get_name(Player player)
{
	return player.name;
}

void set_name(Player player, String value)
{
	player.name = value;
}

/* bet */
float get_bet(Player player)
{
	return player.bet;
}

void set_bet(Player player, float value)
{
	player.bet = value;  
}

/* balance */
float get_balance(Player player)
{
	return player.balance;
}

void set_balance(Player player, float value)
{
	player.balance = value;  
}

/* wins */
int get_wins(Player player)
{
	return player.wins;
}

void set_wins(Player player, int value)
{
	player.wins = value;
}

/* losses */
int get_losses(Player player)
{
	return player.losses;
}

void set_losses(Player player, int value)
{
	player.losses = value;
}

/* pushes */
int get_pushes(Player player)
{
	return player.pushes;
}

void set_pushes(Player player, int value)
{
	player.pushes = value;
}

/* constructors */
Player Player1(int newBalance)
{
	return new Player(newBalance, new Hand1(), 0, 0, 0, 0, Defaults.PlayerImage, Defaults.PlayerName, null, null);    ///// ?? last 2
}

Player Player2()
{
	return Player1(-1);
}

/* other functions from the class Player */
/* increases the bet amount each time a bet is added to the hand */ 
void increaseBet(Player player, float amt)
{
	if ((player.balance - (player.bet + amt)) >= 0)
		player.bet += amt; 
	else 
		error();                // this corresponds to throwing an exception "you dont have enought money to make this bet"
}

/* places the bet and substracts from the account */
void placeBet(Player player)
{
	if ((player.balance - player.bet) >= 0)
		player.balance = player.balance - player.bet;
	else 
		error();                // this corresponds to throwing an exception "you do not have enough money to make this bet"
}

/* creates a new Hand for the player */
Hand newHand(Player player)
{
	player.hand = new Hand1();
	
	return player.hand;
}

/* set the bet value to 0 */
void clearBet(Player player)
{
	player.bet = 0;
} 

/* check if the player has blackjack */
bool hasBlackJack(Player player)
{
	if (getSumOfHand(player.hand) == 21)
		return true; 
	else
		return false;
}

/* check if the current player has bust */
bool hasBust(Player player)
{
	if (getSumOfHand(player.hand) > 21)
		return true;
	else 
		return false; 
}

/* player has hit, draw a card from the deck and add it to the player's hand */
void hit(Player player)
{
	Card c = draw(player.currentDeck);
	add(player.hand.cards, c);	
}

/* player has chosen to double down, double the player's bet and hit once */
void doubleDown(Player player)
{
	increaseBet(player, player.bet);
//	player.balance = player.balance - (player.bet / 2);
	hit(player);
}


/* data to store a black jack game */
data BlackJackGame{
	Deck deck;
	Player dealer;
	Player player;
}

/* get/set functions */
/* player */
Player get_player(BlackJackGame blackJackGame)
{
	return blackJackGame.player;
}

/* dealer */ 
Player get_dealer(BlackJackGame blackJackGame)
{
	return blackJackGame.dealer;
}

/* deck */
Deck get_deck(BlackJackGame blackJackGame)
{
	return blackJackGame.deck;
}

/* constructor */
BlackJackGame BlackJackGame1(int initBalance)
{
	return new BlackJackGame(null, Player1(), Player2(initBalance));	
}

/* functions corresponding to the methods from BlackJackGame class */
void dealNewGame(BlackJackGame blackJackGame)
{
	blackJackGame.deck = Deck1();
	shuffle(blackJackGame.deck);	
	
	newHand(blackJackGame.player);
	newHand(blackJackGame.dealer);

	int i = 0;
	while (i < 2)
	{
		Card c = draw(blackJackGame.deck);
		add(blackJackGame.player.hand.cards, c);

		Card d = draw(blackJackGame.deck);		
		if (i == 1)
			d.isCardUp = false; 
		add(blackJackGame.dealer.hand.cards, d);

		i++;
	}
	blackJackGame.player.currentDeck = blackJackGame.deck;
	blackJackGame.dealer.currentDeck = blackJackGame.deck; 
}

/* function to finish the dealer's hand */
void dealerPlay(BlackJackGame blackJackGame)
{
	(get_ith(blackJackGame.dealer.hand.cards, 1)).isCardUp = true;
	
	if (getSumOfHand(blackJackGame.dealer.hand) < 21)
	{
		hit(blackJackGame.dealer);
		dealerPlay(blackJackGame);
	}
}

/* update the player's record with a loss */
void playerLose(BlackJackGame blackJackGame)
{
	blackJackGame.player.losses += 1; 
}

/* update the player's record with a win */
void playerWin(BlackJackGame blackJackGame)
{
	blackJackGame.player.balance += blackJackGame.player.bet * 2; 
	blackJackGame.player.wins += 1; 
}


