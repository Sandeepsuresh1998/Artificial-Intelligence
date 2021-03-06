#include "ClueReasoner.h"
#include <cstring> to sat_solver.cpp
#include <stdlib.h> to zchaff_dbase.cpp
using namespace std;

int ClueReasoner::GetPlayerNum(string player)
{	
	if (player == case_file)
		return num_players;
	
	for (int i = 0; i < num_players; i++)
		if (player == players[i])
			return i;
			
	cout<<"Illegal player: "<<player<<endl;
	return -1;
}

int ClueReasoner::GetCardNum(string card)
{
	for (int i = 0; i < num_cards; i++)
		if (card == cards[i])
			return i;
			
	cout<<"Illegal card: "<<card<<endl;
	return -1;
}

int ClueReasoner::GetPairNum(int player, int card) 
{
	return player * num_cards + card + 1;
}

int ClueReasoner::GetPairNum(string player, string card) 
{
	return GetPairNum(GetPlayerNum(player), GetCardNum(card));
}

int ClueReasoner::Query(string player, string card) 
{
	return solver->TestLiteral(GetPairNum(player,card));
}

string ClueReasoner::QueryString(int return_code)
{
	if (return_code == kFalse)
		return "n";
	else if (return_code == kTrue)
		return "Y";
	else if (return_code == kUnknown)
		return "-";
	else
		return "X";
}

void ClueReasoner::PrintNotepad()
{
	for (int i = 0; i < num_players; i++)
		cout<<"\t"<<players[i];
	cout<<"\t"<<case_file<<endl;
	
	for (int i = 0; i < num_cards; i++)
	{
		cout<<cards[i]<<"\t";
		for (int j = 0; j < num_players; j++)
			cout<<QueryString(Query(players[j], cards[i]))<<"\t";
		
		cout<<QueryString(Query(case_file, cards[i]))<<endl;
	}
}
	
void ClueReasoner::AddInitialClauses()
{
	/* The following code is given as an example to show how to create Clauses and post them to the solver. SatSolver.h uses the following typedefs:
		typedef int Literal;
		typedef std::vector<Literal> Clause;
		
	That is, a Literal (a propositional variable or its negation) is defined as a positive or a negative (meaning that it is in negated form, as in -p or -q) integer, and a Clause is defined as a vector of Literals.
	
	The function GetPairNum(p, c) returns the literal that corresponds to card c being at location p (either a player's or the case_file). 
	See ClueReasoner.h, lines 7-31 for a definition of the arrays and variables that you can use in your implementation. 
	*/

	// Each card is in at least one place (including the case file).
	for (int c = 0; c < num_cards; c++)	// Iterate over all cards.
	{
		Clause clause;
		for (int p = 0; p <= num_players; p++)	// Iterate over all players, including the case file (as a possible place for a card).
			clause.push_back(GetPairNum(p, c)); // Add to the clause the literal that states 'p has c'.
		
		solver->AddClause(clause);
	}
//----------------------------------------------------------------------------------------------
	
	// If a card is in one place, it cannot be in another place.
	// TO BE IMPLEMENTED AS AN EXERCISE

	for (int c = 0; c < num_cards; c++) // Iterate over all cards 
	{
		for (int p = 0; p <= num_players; p++) //It's equal to the num players because of the case file? 
		{
			for (int k = 0; k <= num_players; k++) 
			{
				Clause clause;
				//Make sure we are not dealing with the same player
				if (k == p) 
				{
					continue;
				}
				else 
				{
					//Because player p has card c, player k cannot have card c
					clause.push_back(GetPairNum(p,c) * -1);
					clause.push_back(GetPairNum(k,c) * -1);
				}
				solver->AddClause(clause);
			}
		}
	}
//----------------------------------------------------------------------------------------------
	
	// At least one card of each category is in the case file.
	// TO BE IMPLEMENTED AS AN EXERCISE

	//Iterate through all player cards
	Clause sus_clause;
	for (int i = 0; i < num_suspects; i++) 
	{
		//Add clause that one player card is in the case file location
		sus_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(suspects[i])));
	}
	solver->AddClause(sus_clause);

	Clause weapon_clause;
	for (int i = 0; i < num_weapons; i++) 
	{
		//Add clause that at least one weapon is in casefile location
		weapon_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(weapons[i])));
	}
	solver->AddClause(weapon_clause);

	Clause room_clause;
	for (int i = 0; i < num_rooms; i++) 
	{
		//Add clause that at least one weapon is in casefile location
		room_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(rooms[i])));
	}
	solver->AddClause(room_clause);
 

//----------------------------------------------------------------------------------------------

	// No two cards in each category can both be in the case file.
	// TO BE IMPLEMENTED AS AN EXERCISE


	// No two cards for suspect category
	for (int i = 0; i < num_suspects; i++) 
	{
		
		for (int k = 0; k < num_suspects; k++) 
		{	
			Clause sus_clause;
			if(i == k){
				continue;
			}
			//If suspect i, is in the casefile, then suspect k cannot be
			sus_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(suspects[i])) * -1);
			sus_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(suspects[k])) * -1);
			solver->AddClause(sus_clause);
		}
		
	}

	for (int i = 0; i < num_weapons; i++) 
	{
		for (int k = 0; k < num_weapons; k++) 
		{
			Clause weapon_clause;
			if(i == k)
			{
				continue;
			}
			//If weapon i, is in the casefile, then weapon k cannot be
			weapon_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(weapons[i])) * -1);
			weapon_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(weapons[k])) * -1);
			solver->AddClause(weapon_clause);
		}
		
	}

	for (int i = 0; i < num_rooms; i++) 
	{
		
		for (int k = 0; k < num_rooms; k++) 
		{
			Clause room_clause;
			if(i == k) 
			{
				continue;
			}
			//If room i, is in the casefile, then room k cannot be
			room_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(rooms[i])) * -1);
			room_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(rooms[k])) * -1);
			solver->AddClause(room_clause);
		}
		
	}



}

void ClueReasoner::Hand(string player, string cards[3])
{
	// GetPlayerNum returns the index of the player in the players array (not the suspects array). 
	// Remember that the players array is sorted wrt the order that the players play. 
	// Also note that, player_num (not to be confused with num_players) is a private variable of 
	// the ClueReasoner class that is initialized when this function is called.
	player_num = GetPlayerNum(player);
	// TO BE IMPLEMENTED AS AN EXERCISE

	//Adding the fact that my player has the cards to the knowledge base
	for (int i = 0; i < 3; i++) {
		Clause clause; 
		clause.push_back(GetPairNum(player_num, GetCardNum(cards[i])));
		solver->AddClause(clause);
	}
}

void ClueReasoner::Suggest(string suggester, string card1, string card2, string card3, string refuter, string card_shown)
{
	// // Note that in the Java implementation, the refuter and the card_shown can be NULL. 
	// // In this C++ implementation, NULL is translated to be the empty string "".
	// // To check if refuter is NULL or card_shown is NULL, you should use if(refuter == "") or if(card_shown == ""), respectively.
	
	// TO BE IMPLEMENTED AS AN EXERCISE

	//If we have a refuter
	if(refuter != "") {
	
		//If we know the card shown
		if(card_shown != "") {
			//Immediately we know that refuter has card shown
			Clause refuter_clause;
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card_shown)));
			solver->AddClause(refuter_clause);
		} else {
			//Immediately we know that the refuter has at least one of the cards
			Clause refuter_clause;
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card1)));
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card2)));
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card3)));
			solver->AddClause(refuter_clause);
		}

	} else {

		//Iterate through all players and say that they don't have the cards
		for (int i = 0; i < num_players; i++) {

			//We can't say suggester doesn't have the cards suggested
			if (i == GetPlayerNum(suggester)) {
				continue;
			}
			cout << i << endl;

			Clause card1_clause;
			Clause card2_clause;
			Clause card3_clause;

			card1_clause.push_back(GetPairNum(i, GetCardNum(card1)) * -1);
			card2_clause.push_back(GetPairNum(i, GetCardNum(card2)) * -1);
			card3_clause.push_back(GetPairNum(i, GetCardNum(card3)) * -1);

			solver->AddClause(card1_clause);
			solver->AddClause(card2_clause);
			solver->AddClause(card3_clause);
		
		}
	}
	
	
}

void ClueReasoner::Accuse(string suggester, string card1, string card2, string card3, bool is_correct)
{
	// TO BE IMPLEMENTED AS AN EXERCISE (you don't need to implement this)
}

